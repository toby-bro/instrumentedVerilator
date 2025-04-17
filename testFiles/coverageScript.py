#!/usr/bin/env python3

import argparse
import concurrent.futures
import logging
import os
import re
import signal
import subprocess
from typing import Any

logger = logging.getLogger(__name__)
logging.basicConfig(level=logging.INFO, format='%(levelname)s - %(message)s')


def process_test(test: str, test_path: str, src_path: str) -> str:
    try:
        verilator_cmd = f"""$VERILATOR_ROOT/bin/verilator --cc --binary \
                            -Wno-MULTIDRIVEN --Wno-UNOPTFLAT --Wno-NOLATCH \
                            --Wno-WIDTHTRUNC --Wno-CMPCONST --Wno-WIDTHEXPAND --Wno-UNSIGNED \
                            {test_path}/obj_dir_example_sim_{test}/top.sv \
                            -CFLAGS '-I/testFiles/include -I{test_path}/obj_dir_example_sim_{test} -g' \
                            --Mdir {test_path}/obj_dir_example_sim_{test}/obj_dir"""

        p = subprocess.Popen([verilator_cmd], shell=True, cwd=src_path)  # noqa: S602
        p.wait()
        if p.returncode != 0:
            return f'ERROR:{test}:Verilator compilation failed'

        binary_path = f'{test_path}/obj_dir_example_sim_{test}/obj_dir/Vtop'
        if os.path.exists(binary_path):
            execute_cmd = f'{binary_path}'
            p = subprocess.Popen([execute_cmd], shell=True, cwd=src_path)  # noqa: S602
            p.wait()
            if p.returncode != 0:
                return f'ERROR:{test}:Execution failed'
            return f'SUCCESS:{test}'
        return f'ERROR:{test}:Binary not found'

    except Exception as e:
        logger.error(f'Exception in worker process for test {test}: {e}')
        return f'ERROR:{test}:{e!s}'


def main(test_path: str, src_path: str) -> None:
    if not os.path.isdir(test_path):
        logger.error(f'{test_path} is not a valid directory')
        return
    if not os.path.isdir(src_path):
        logger.error(f'{src_path} is not a valid directory')
        return

    subdirectories = [entry for entry in os.listdir(test_path) if os.path.isdir(os.path.join(test_path, entry))]
    logger.info('Found test folder') if subdirectories else logger.warning(f'No subdirectories found in {test_path}')

    test_numbers = []
    for name in subdirectories:
        match = re.search(r'(?<=obj_dir_example_sim_)\d+', name)
        if match:
            test_numbers.append(match.group())

    logger.info(f'Number of tests: {len(test_numbers)}')

    os.makedirs('/testFiles/coverage_reports', exist_ok=True)

    successful_tests = []

    original_sigint = signal.getsignal(signal.SIGINT)

    def sigint_handler(sig: Any, frame: Any) -> None:  # noqa: ARG001
        logger.warning('Interrupted by user. Finishing current tests...')
        signal.signal(signal.SIGINT, original_sigint)

    signal.signal(signal.SIGINT, sigint_handler)

    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as executor:
        future_to_test = {
            executor.submit(process_test, test, test_path, src_path): (i, test) for i, test in enumerate(test_numbers)
        }

        completed_tests = 0
        for future in concurrent.futures.as_completed(future_to_test):
            _, test = future_to_test[future]
            completed_tests += 1

            try:
                result = future.result()
                logger.info(f'Completed test {completed_tests}/{len(test_numbers)}: {result}')

                if result.startswith('SUCCESS'):
                    successful_tests.append(test)

            except Exception as exc:
                logger.error(f'Test {test} generated an exception: {exc}')

    logger.info('Creating final coverage report')
    gcovr_merge = "gcovr --html --html-details -f '.*\\.cpp$' -e '(.*/)?(V3Coverage\\.cpp|V3CoverageJoin\\.cpp|V3EmitCMake\\.cpp|V3EmitXml\\.cpp|V3ExecGraph\\.cpp|V3GraphTest\\.cpp|V3HierBlock\\.cpp|V3Trace\\.cpp|V3TraceDecl\\.cpp)$' -o /testFiles/coverage_reports/coverage_report.html --root /verilator/src"  # noqa: E501
    p = subprocess.Popen([gcovr_merge], shell=True, cwd=src_path)  # noqa: S602
    p.wait()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        prog='coverageScript',
        description='Runs Transfuzz generated circuits and compiles code coverage across all circuits',
    )
    parser.add_argument(
        'test_path',
        default='/testFiles/verismith',
        nargs='?',
        help='Path to test directory (default: /testFiles/transfuzzTestFiles)',
    )
    parser.add_argument(
        'verilator_src_path',
        default='/verilator/src',
        nargs='?',
        help='Path to Verilator source code (default: /verilator/src)',
    )

    args = parser.parse_args()

    try:
        main(args.test_path, args.verilator_src_path)
    except KeyboardInterrupt:
        logger.warning('Script interrupted by user. Exiting.')
