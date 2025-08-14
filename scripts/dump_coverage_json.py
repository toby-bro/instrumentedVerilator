#!/usr/bin/env python3
import argparse
import asyncio
import logging
import random
import shlex
import subprocess
from pathlib import Path
from typing import Dict, List, TypedDict

ROOT = Path(__file__).resolve().parents[1]
TESTFILES = ROOT / 'testFiles'
CHIMERA_DEFAULT = ROOT.parent / 'chimera' / '3k_programs_for_bugs'
NAIVE_ROOT = ROOT / 'naive'


class ToolConfig(TypedDict):
    image: str
    container: str
    get_exec_cmd_make: List[str]
    coverage_cmd: str


TOOLS: Dict[str, ToolConfig] = {
    'verilator': {
        'image': 'ghcr.io/toby-bro/instrumentedverilator:main',
        'container': 'cov-json-verilator',
        'get_exec_cmd_make': ['make', 'getExecOneFileCmd'],
        'coverage_cmd': (
            "fastcov -o {out} -b -d /verilator/src "
            "--exclude-glob '*.[hly]' --include .cpp --exclude /usr/include "
            "V3Coverage.cpp V3CoverageJoin.cpp V3EmitCMake.cpp V3EmitXml.cpp "
            "V3ExecGraph.cpp V3GraphTest.cpp V3HierBlock.cpp V3Trace.cpp V3TraceDecl.cpp "
            "V3EmitV.cpp V3TSP.cpp V3Scoreboard.cpp V3Stats.cpp V3ProtectLib.cpp "
            "V3Broken.cpp V3Interface.cpp"
        ),
    },
    'yosys': {
        'image': 'ghcr.io/toby-bro/instrumentedyosys:main',
        'container': 'cov-json-yosys',
        'get_exec_cmd_make': ['make', 'getExecYosysFileCmd'],
        'coverage_cmd': (
            "fastcov -o {out} -b -d /yosys/ --exclude-glob '*.[hly]' --include .cc .cpp --exclude /usr/include"
        ),
    },
    'slang': {
        'image': 'ghcr.io/toby-bro/instrumentedslang:main',
        'container': 'cov-json-slang',
        'get_exec_cmd_make': ['make', 'getExecSlangFileCmd'],
        'coverage_cmd': (
            "fastcov -o {out} -b -d /slang/ "
            "--exclude-glob '*.[hly]' --include .cc .cpp --exclude /usr/include "
            "analysis/ diagnostics/ driver/ numeric/ syntax/ text/ util/ /slang/build "
        ),
    },
}


async def run(cmd: List[str], check: bool = True, capture: bool = False, cwd: str | None = None) -> str:
    logging.debug('+ %s', ' '.join(shlex.quote(c) for c in cmd))
    # Basic validation to avoid executing untrusted input
    if any((not isinstance(a, str)) or ('\n' in a or '\r' in a) for a in cmd):
        raise ValueError('Invalid command argument detected')
    allowed = {'docker', 'make'}
    if not cmd or cmd[0] not in allowed:
        raise ValueError(f'Command not allowed: {cmd[0] if cmd else cmd}')

    if capture:
        proc = await asyncio.create_subprocess_exec(
            *cmd,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            cwd=cwd,
        )
        stdout, stderr = await proc.communicate()
        if check and proc.returncode != 0:
            returncode = proc.returncode or -1
            raise subprocess.CalledProcessError(returncode, cmd, stdout, stderr)
        return stdout.decode().strip()

    proc = await asyncio.create_subprocess_exec(*cmd, cwd=cwd)
    await proc.wait()
    if check and proc.returncode != 0:
        returncode = proc.returncode or -1
        raise subprocess.CalledProcessError(returncode, cmd)
    return ''


def pick_verilog_files(src_dir: Path, n: int) -> List[Path]:
    files = [p for p in src_dir.rglob('*.v') if p.is_file()]
    if len(files) == 0:
        files = [p for p in src_dir.rglob('*.sv') if p.is_file()]
    if len(files) < n:
        return files
    return random.sample(files, n)


async def start_container(tool: str) -> str:
    cfg = TOOLS[tool]
    container = cfg['container']
    image = cfg['image']
    # Mount testFiles, naive, and chimera root; workdir /testFiles
    # Stop any previous container with same name (best-effort)
    await run(['docker', 'stop', container], check=False)
    await run(
        [
            'docker',
            'run',
            '-d',
            '--rm',
            '--name',
            container,
            '-v',
            f'{TESTFILES}:/testFiles',
            '-v',
            f'{NAIVE_ROOT}:/naive',
            '-v',
            f'{ROOT.parent / "chimera"}:/chimera',
            '--workdir',
            '/testFiles',
            image,
            'sleep',
            '3600',
        ],
    )
    return container


async def stop_container(container: str) -> None:
    await run(['docker', 'stop', container], check=False)


async def get_exec_template(tool: str) -> str:
    # Use Makefile helpers to get the per-file command template
    out = await run(TOOLS[tool]['get_exec_cmd_make'], capture=True, cwd=str(ROOT))
    # It may echo quotes/shell constructs. We'll execute via bash -lc inside container.
    return out.strip()


async def exec_file_in_tool(container: str, tmpl: str, file_path_in_container: str) -> None:
    # Replace common placeholders used in Makefile helpers
    if 'file.sv' in tmpl:
        cmd = tmpl.replace('file.sv', file_path_in_container)
    elif 'file.v' in tmpl:
        cmd = tmpl.replace('file.v', file_path_in_container)
    else:
        # Last resort: append path (not expected for provided Makefile)
        cmd = f'{tmpl} {shlex.quote(file_path_in_container)}'
    # Use bash -lc to respect quoting inside template
    await run(['docker', 'exec', container, '/bin/bash', '-lc', cmd], check=False)


async def dump_json_coverage(container: str, tool: str, out_basename: str) -> None:
    out_path = f'/testFiles/{out_basename}'
    cov_cmd = TOOLS[tool]['coverage_cmd'].format(out=out_path)
    await run(['docker', 'exec', container, '/bin/bash', '-lc', cov_cmd])


async def run_batch(fuzzer: str, dataset_root: Path, n: int, templates: Dict[str, str]) -> None:
    src_dir = dataset_root / fuzzer
    if not src_dir.is_dir():
        logging.warning('Skipping %s: %s does not exist', fuzzer, src_dir)
        return
    files = pick_verilog_files(src_dir, n)
    if not files:
        logging.warning('No .v files found in %s; skipping %s', src_dir, fuzzer)
        return
    logging.info('[%s] Selected %d files from %s', fuzzer, len(files), src_dir)

    # Start all containers in parallel
    container_tasks = [start_container(tool) for tool in TOOLS]
    containers_list = await asyncio.gather(*container_tasks)
    containers = dict(zip(TOOLS.keys(), containers_list, strict=True))

    try:
        # Process files for each tool in parallel
        async def process_tool_files(tool: str, container: str) -> None:
            for f in files:
                chimera_root = (ROOT.parent / 'chimera').resolve()
                naive_root = NAIVE_ROOT.resolve()
                try:
                    rel = f.resolve().relative_to(chimera_root)
                    file_in_container = f'/chimera/{rel.as_posix()}'
                except ValueError:
                    try:
                        rel = f.resolve().relative_to(naive_root)
                        file_in_container = f'/naive/{rel.as_posix()}'
                    except ValueError:
                        logging.warning('Skipping file outside mounted roots: %s', f)
                        continue
                await exec_file_in_tool(container, templates[tool], file_in_container)

        # Run all tools in parallel for processing files
        tool_tasks = [process_tool_files(tool, container) for tool, container in containers.items()]
        await asyncio.gather(*tool_tasks)

        # Dump coverage for all tools in parallel
        dump_tasks = [
            dump_json_coverage(container, tool, f'coverage-{tool}-{fuzzer}.json')
            for tool, container in containers.items()
        ]
        await asyncio.gather(*dump_tasks)

        for tool in containers:
            logging.info('[%s] Wrote coverage-%s-%s.json', fuzzer, tool, fuzzer)

    finally:
        # Stop all containers in parallel
        stop_tasks = [stop_container(container) for container in containers.values()]
        await asyncio.gather(*stop_tasks, return_exceptions=True)


def _resolve_source_dir(preferred: Path) -> Path | None:
    src_dir = preferred.resolve()
    if src_dir.is_dir():
        return src_dir
    candidates = [
        NAIVE_ROOT,
        ROOT / 'testFiles' / 'verismith',
        ROOT / 'testFiles' / 'transfuzzTestFiles',
        ROOT / 'testFiles',
    ]
    for cand in candidates:
        if cand.is_dir():
            logging.warning('Source dir %s missing; falling back to %s', src_dir, cand)
            return cand
    return None


def main() -> int:
    logging.basicConfig(level=logging.INFO, format='[%(levelname)s] %(message)s')
    ap = argparse.ArgumentParser(description='Run N .v files in containers and dump fastcov JSON for Verilator/Yosys')
    ap.add_argument(
        '--source-dir',
        type=Path,
        default=CHIMERA_DEFAULT,
        help='Directory containing .v files, can be the dataset root (default: ../chimera/3k_programs_for_bugs)',
    )
    ap.add_argument('-n', '--count', type=int, default=50, help='Number of files to run per fuzzer (default: 50)')
    ap.add_argument(
        '--fuzzers',
        nargs='*',
        default=['vloghammer', 'verismith', 'transfuzz'],
        help='Fuzzer subfolders to run in order (default: vloghammer verismith transfuzz)',
    )
    args = ap.parse_args()

    src_dir = _resolve_source_dir(args.source_dir)
    if src_dir is None:
        logging.error('Source dir not found and no local fallback exists: %s', args.source_dir)
        return 1

    TESTFILES.mkdir(parents=True, exist_ok=True)
    (TESTFILES / 'synth_out').mkdir(parents=True, exist_ok=True)

    # Run everything async since we removed sync functions
    return asyncio.run(main_async(args.fuzzers, src_dir, args.count))


async def main_async(fuzzers: List[str], src_dir: Path, count: int) -> int:
    # Prepare per-tool exec templates once
    templates = {tool: await get_exec_template(tool) for tool in TOOLS}

    # Run batches sequentially, but with parallel container execution within each batch
    for fuzzer in fuzzers:
        await run_batch(fuzzer, src_dir, count, templates)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
