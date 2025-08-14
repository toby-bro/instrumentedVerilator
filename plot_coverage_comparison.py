import glob
import logging
import os
import re
import subprocess
from shutil import which
from typing import Dict, List, Optional, Tuple

import matplotlib.pyplot as plt
import pandas as pd
import seaborn as sns
from matplotlib.axes import Axes

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# Configuration
FUZZERS = {
    'Transfuzz': 'testFiles/transfuzzTestFiles',
    'VeriSmith': 'testFiles/verismith',
    # 'VlogHammer': 'testFiles/vloghammer' # Add when available
}
TOOLS = ['Verilator', 'Slang', 'Yosys']  # Default display order; actual tools used are inferred from data
NUM_FILES = 50


def get_test_files(fuzzer_path: str, num_files: int) -> List[str]:
    """Legacy helper (unused now)."""
    test_cases = [d for d in os.listdir(fuzzer_path) if os.path.isdir(os.path.join(fuzzer_path, d))]
    files = []
    for case in sorted(test_cases)[:num_files]:
        file_path = os.path.join(fuzzer_path, case, 'top.sv')
        if os.path.exists(file_path):
            files.append(file_path)
    return files


# run_command was used in older drafts; removed to avoid unused subprocess warnings.


# -------------------- fastcov integration --------------------
_FASTCOV_LINE_RE = re.compile(r'^line:\s*([0-9]+\.?[0-9]*)%\s*\((\d+)\s+of\s+(\d+)\)')
_FASTCOV_FUNC_RE = re.compile(r'^function:\s*([0-9]+\.?[0-9]*)%\s*\((\d+)\s+of\s+(\d+)\)')
_FASTCOV_BRANCH_RE = re.compile(r'^branch:\s*([0-9]+\.?[0-9]*)%\s*\((\d+)\s+of\s+(\d+)\)')


def _parse_fastcov_summary_output(text: str) -> Optional[Tuple[float, float, float]]:
    """Return (line_pct, func_pct, branch_pct) from fastcov_summary output, or None on parse error."""
    line_pct: Optional[float] = None
    func_pct: Optional[float] = None
    branch_pct: Optional[float] = None
    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            continue
        m = _FASTCOV_LINE_RE.match(line)
        if m:
            line_pct = float(m.group(1))
            continue
        m = _FASTCOV_FUNC_RE.match(line)
        if m:
            func_pct = float(m.group(1))
            continue
        m = _FASTCOV_BRANCH_RE.match(line)
        if m:
            branch_pct = float(m.group(1))
            continue
    if line_pct is None or func_pct is None or branch_pct is None:
        return None
    return line_pct, func_pct, branch_pct


def fastcov_summary(json_path: str) -> Optional[Tuple[float, float, float]]:
    """Run fastcov_summary on a JSON file and parse percentages.

    Returns (line_pct, func_pct, branch_pct) or None if command fails or output can't be parsed.
    """
    exe = which('fastcov_summary')
    if not exe:
        logging.warning('fastcov_summary executable not found in PATH.')
        return None
    # Basic safety: ensure path exists and is a file, and contains no newlines
    if not os.path.isfile(json_path) or '\n' in json_path or '\r' in json_path:
        logging.warning(f'Invalid JSON path for fastcov_summary: {json_path!r}')
        return None
    try:
        # Additional safety: simple allowlist for executable basename
        if os.path.basename(exe) != 'fastcov_summary':
            logging.warning('Unexpected executable for fastcov_summary: %s', exe)
            return None
        res = subprocess.run(  # noqa: S603
            [exe, json_path],
            check=True,
            capture_output=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as e:
        logging.warning(f'fastcov_summary failed for {json_path}: {e}')
        return None
    parsed = _parse_fastcov_summary_output(res.stdout)
    if parsed is None:
        logging.warning(f'Could not parse fastcov_summary output for {json_path}\n{res.stdout}')
    return parsed


def _canonical_tool(tool_token: str) -> str:
    """Normalize tool token to standard display name."""
    t = tool_token.lower()
    if t in {'verilator', 'ver'}:
        return 'Verilator'
    if t in {'yosys'}:
        return 'Yosys'
    if t in {'slang'}:
        return 'Slang'
    return tool_token.capitalize()


def _canonical_fuzzer(fuz_token: str) -> str:
    """Normalize fuzzer token to standard display name."""
    f = fuz_token.strip().replace('_', '-')
    low = f.lower()
    if low in {'vloghammer', 'vlog-hammer', 'vh'}:
        return 'VlogHammer'
    if low in {'verismith', 'veri-smith', 'vs'}:
        return 'VeriSmith'
    if low in {'transfuzz', 'trans-fuzz', 'tf'}:
        return 'Transfuzz'
    return f


def collect_data_from_fastcov(json_dirs: Optional[List[str]] = None) -> pd.DataFrame:
    """Scan for coverage-<tool>-<fuzzer>.json and collect coverage via fastcov_summary.

    By default, looks under testFiles/.
    """
    search_dirs = json_dirs or ['testFiles']
    patterns = [os.path.join(d, 'coverage-*-*.json') for d in search_dirs]
    files: List[str] = []
    for pat in patterns:
        files.extend(glob.glob(pat))

    if not files:
        logging.warning(
            'No fastcov JSON files found (expected pattern coverage-<tool>-<fuzzer>.json). Using empty dataset.',
        )
        return pd.DataFrame(columns=['Tool', 'Fuzzer', 'Coverage', 'Type'])

    rows: List[Dict[str, object]] = []
    for path in sorted(files):
        base = os.path.basename(path)
        # Expect coverage-<tool>-<fuzzer>.json
        m = re.match(r'coverage-([A-Za-z0-9]+)-([A-Za-z0-9_.\-]+)\.json$', base)
        if not m:
            logging.debug(f'Skipping non-matching file name: {base}')
            continue
        tool_tok, fuz_tok = m.group(1), m.group(2)
        tool = _canonical_tool(tool_tok)
        fuzzer = _canonical_fuzzer(fuz_tok)
        parsed = fastcov_summary(path)
        if parsed is None:
            continue
        line_pct, func_pct, branch_pct = parsed
        rows.append({'Tool': tool, 'Fuzzer': fuzzer, 'Coverage': branch_pct, 'Type': 'Branch'})
        rows.append({'Tool': tool, 'Fuzzer': fuzzer, 'Coverage': line_pct, 'Type': 'Line'})
        rows.append({'Tool': tool, 'Fuzzer': fuzzer, 'Coverage': func_pct, 'Type': 'Function'})

    return pd.DataFrame(rows)


def parse_lcov_summary(summary_text: str) -> Tuple[float, float, float]:
    """Legacy helper (unused now)."""
    lines_cov, funcs_cov, branches_cov = 0.0, 0.0, 0.0
    for line in summary_text.splitlines():
        if 'lines......' in line:
            match = re.search(r'(\d+\.\d+)\s*%', line)
            if match:
                lines_cov = float(match.group(1))
        elif 'functions..' in line:
            match = re.search(r'(\d+\.\d+)\s*%', line)
            if match:
                funcs_cov = float(match.group(1))
        elif 'branches...' in line:
            match = re.search(r'(\d+\.\d+)\s*%', line)
            if match:
                branches_cov = float(match.group(1))
    return lines_cov, funcs_cov, branches_cov


def get_coverage_for_tool(tool: str, fuzzer: str) -> Tuple[float, float, float]:
    """Legacy placeholder (unused now)."""
    logging.info('Simulating coverage for %s on %s', tool, fuzzer)
    return 0.0, 0.0, 0.0


def collect_data() -> pd.DataFrame:
    """Legacy aggregation (unused now)."""
    return pd.DataFrame([])


# --- Plotting helpers to keep plot_coverage simple and lint-friendly ---
def _aggregate_data_for_plot(dfi: pd.DataFrame) -> pd.DataFrame:
    """Aggregate coverage to mean and 95% CI by (Tool, Fuzzer, Type)."""
    group_cols = ['Tool', 'Fuzzer', 'Type']
    if 'Experiment' in dfi.columns:
        agg = dfi.groupby(group_cols, as_index=False)['Coverage'].agg(['mean', 'std', 'count']).reset_index()
        agg['se'] = agg['std'] / (agg['count'] ** 0.5)
        agg['ci'] = 1.96 * agg['se']
    else:
        agg = dfi.groupby(group_cols, as_index=False)['Coverage'].agg(['mean']).reset_index()
        agg['ci'] = 0.0
    return agg


def _compute_plot_settings(fuzzers_order: List[str]) -> Tuple[
    List[str],
    Dict[str, float],
    Dict[str, str],
    Dict[str, Tuple[float, float, float]],
]:
    """Return static settings and color mapping per fuzzer."""
    types_order = ['Branch', 'Line', 'Function']
    offsets = {'Branch': -0.2, 'Line': 0.0, 'Function': 0.2}
    markers = {'Branch': 's', 'Line': 'o', 'Function': 'D'}
    palette = sns.color_palette(n_colors=len(fuzzers_order))
    colors = {f: palette[i] for i, f in enumerate(fuzzers_order)}
    return types_order, offsets, markers, colors


def _build_positions(tools_order: List[str], fuzzers_order: List[str]) -> Tuple[List[int], List[str]]:
    """Build x-axis positions and labels for tool-fuzzer combinations."""
    base_positions: list[int] = []
    xticklabels: list[str] = []
    for tool in tools_order:
        for fuz in fuzzers_order:
            base_positions.append(len(base_positions))
            xticklabels.append(f'{tool}\n{fuz}')
    return base_positions, xticklabels


def _plot_block(
    ax: Axes,
    idx: int,
    block: pd.DataFrame,
    color: Tuple[float, float, float],
    markers: Dict[str, str],
    offsets: Dict[str, float],
    types_order: List[str],
) -> None:
    """Plot coverage points with error bars for a single tool-fuzzer combination."""
    line_x, line_y = [], []
    for typ in types_order:
        row = block[block['Type'] == typ]
        if row.empty:
            continue
        x = idx + offsets.get(typ, 0.0)
        y = float(row['mean'].iloc[0])
        ci = float(row['ci'].iloc[0])
        ax.errorbar(
            x,
            y,
            yerr=ci,
            fmt=markers.get(typ, 'o'),
            color=color,
            capsize=3,
            markersize=6,
            linestyle='None',
            alpha=0.9,
        )
        line_x.append(x)
        line_y.append(y)
    if len(line_x) >= 2:
        order = sorted(range(len(line_x)), key=lambda i: line_x[i])
        sx = [line_x[i] for i in order]
        sy = [line_y[i] for i in order]
        ax.plot(sx, sy, color=color, alpha=0.6, linewidth=1)


def _render_combined_plot(ax: Axes, df: pd.DataFrame) -> None:
    """Render the main combined plot with error bars and linking lines."""
    # Use tools present in data (fallback to default order when equal)
    present_tools = df['Tool'].unique().tolist()
    tools_order = [t for t in TOOLS if t in present_tools] + [t for t in present_tools if t not in TOOLS]
    fuzzers_order = list(df['Fuzzer'].unique().tolist())
    types_order, offsets, markers, colors = _compute_plot_settings(fuzzers_order)
    agg = _aggregate_data_for_plot(df)
    base_positions, xticklabels = _build_positions(tools_order, fuzzers_order)

    idx = -1
    # Collect per-type points for global linking lines
    type_points: Dict[str, List[Tuple[float, float]]] = {'Branch': [], 'Line': [], 'Function': []}
    for tool in tools_order:
        for fuz in fuzzers_order:
            idx += 1
            block = agg[(agg['Tool'] == tool) & (agg['Fuzzer'] == fuz)]
            if block.empty:
                continue
            _plot_block(ax, idx, block, colors[fuz], markers, offsets, types_order)
            # Accumulate positions for global lines
            for typ in types_order:
                row = block[block['Type'] == typ]
                if row.empty:
                    continue
                x = idx + offsets.get(typ, 0.0)
                y = float(row['mean'].iloc[0])
                type_points[typ].append((x, y))

    ax.set_xticks(list(range(len(base_positions))))
    ax.set_xticklabels(xticklabels)
    ax.set_ylabel('Coverage (%)')
    ax.set_ylim(0, 100)
    ax.set_title('Combined Coverage (Branch, Line, Function) with 95% CI and Linking Lines')

    # Draw three global lines, one per Type, across all groups
    type_line_styles = {'Branch': '--', 'Line': '-', 'Function': ':'}
    type_line_colors = {'Branch': '#888888', 'Line': '#000000', 'Function': '#555555'}
    for typ in types_order:
        pts = sorted(type_points[typ], key=lambda p: p[0])
        if len(pts) >= 2:
            xs = [p[0] for p in pts]
            ys = [p[1] for p in pts]
            ax.plot(
                xs,
                ys,
                linestyle=type_line_styles.get(typ, '-'),
                color=type_line_colors.get(typ, '#333333'),
                linewidth=1.2,
                alpha=0.8,
            )

    from matplotlib.lines import Line2D

    fuzzer_handles = [
        Line2D([0], [0], color=colors[f], marker='o', linestyle='-', alpha=0.8, label=f) for f in fuzzers_order
    ]
    type_handles = [
        Line2D(
            [0],
            [0],
            color=type_line_colors.get(t, 'gray'),
            marker=markers[t],
            linestyle=type_line_styles.get(t, '-'),
            label=t,
        )
        for t in types_order
    ]
    first = ax.legend(handles=fuzzer_handles, title='Fuzzer', bbox_to_anchor=(1.02, 1), loc='upper left')
    ax.add_artist(first)
    ax.legend(handles=type_handles, title='Type', bbox_to_anchor=(1.02, 0), loc='lower left')


def plot_coverage(df: pd.DataFrame) -> None:
    """Thin wrapper: render a single combined plot with error bars and linking lines."""
    if df.empty:
        logging.info('DataFrame is empty, nothing to plot.')
        return
    sns.set_theme(style='whitegrid')
    fig, ax = plt.subplots(figsize=(14, 9))
    _render_combined_plot(ax, df)
    plt.tight_layout()
    out_file = 'combined_coverage_comparison.png'
    plt.savefig(out_file, bbox_inches='tight')
    logging.info(f'Saved plot to {out_file}')
    plt.show()


def main() -> None:
    """Main function to collect and plot data using fastcov_summary over JSON outputs."""
    # Prefer JSON outputs produced by the runner in testFiles/
    df = collect_data_from_fastcov(['testFiles'])  # add more directories if needed
    if df.empty:
        logging.info('No coverage data found from fastcov JSONs. Nothing to plot.')
        return
    plot_coverage(df)


if __name__ == '__main__':
    main()
