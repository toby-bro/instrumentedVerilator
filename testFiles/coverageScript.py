#!/usr/bin/env python3

import argparse
import os
import re
import subprocess


def main(test_path: str, src_path: str) -> None:
    if not os.path.isdir(test_path):
        print(f"{test_path} is not a valid directory")
        return
    if not os.path.isdir(src_path):
        print(f"{src_path} is not a valid directory")
        return

    subdirectories = [entry for entry in os.listdir(test_path) if os.path.isdir(os.path.join(test_path, entry))]
    print("Found test folder") if subdirectories else print("No subdirectories found in {test_path}")

    test_numbers = []
    for name in subdirectories:
        match = re.search(r"(?<=obj_dir_example_sim_)\d+", name)
        if match:
            test_numbers.append(match.group())

    print("Number of tests: ", len(test_numbers))

    coverage_checkpoints = [i for i in range(0, len(test_numbers), 5)]
    for test_count, test in enumerate(test_numbers):
        # First Verilate
        verilator_cmd = f"""$VERILATOR_ROOT/bin/verilator --cc --binary -Wno-MULTIDRIVEN --Wno-UNOPTFLAT --Wno-NOLATCH --Wno-WIDTHTRUNC --Wno-CMPCONST --Wno-WIDTHEXPAND --Wno-UNSIGNED \
                            /verilator/coverage_tests/transfuzzTestFiles/obj_dir_example_sim_{test}/top.sv \
                            -CFLAGS '/verilator/coverage_tests/include -I/verilator/coverage_tests/transfuzzTestFiles/obj_dir_example_sim_{test} -g'\
                            --Mdir /verilator/coverage_tests/transfuzzTestFiles/obj_dir_example_sim_{test}/obj_dir"""
        p = subprocess.Popen([verilator_cmd], shell=True, cwd=src_path)
        p.wait()

        # Second create json for the run
        gcovr_cmd = r"gcovr --html -o /testFiles/coverage_reports/test.html -e '(.*/)?(V3Coverage\.cpp|V3CoverageJoin\.cpp|V3EmitCMake\.cpp|V3EmitXml\.cpp|V3ExecGraph\.cpp|V3GraphTest\.cpp|V3HierBlock\.cpp|V3Trace\.cpp|V3TraceDecl\.cpp|.*\.h)$' --root /verilator/src"
        p = subprocess.Popen([gcovr_cmd], shell=True, cwd=src_path)
        p.wait()

        # For every 5 tests ran, or for every manually selected checkpoint, compile reports and give html report
        # if test_count % 5 == 0 and test_count != 0:
        if test_count in coverage_checkpoints:
            gcovr_merge = f"gcovr --html -a '/verilator/coverage_reports/*.json' -o /verilator/coverage_reports/mergeReport_{test_count}_html.html"
            p = subprocess.Popen([gcovr_merge], shell=True, cwd=src_path)
            p.wait()

    # Third merge jsons and form html
    gcovr_merge = f"gcovr --html --html-details -a '/verilator/coverage_reports/*.json' -o /verilator/coverage_reports/mergeReport_{test_count}_html.html"
    p = subprocess.Popen([gcovr_merge], shell=True, cwd=src_path)
    p.wait()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        prog='coverageScript',
        description='Runs Transfuzz generated circuits and compiles code coverage across all circuits',
    )
    parser.add_argument(
        'test_path',
        default='/verilator/coverage_tests/transfuzzTestFiles',
        nargs='?',
        help='Path to test directory (default: /verilator/coverage_tests/transfuzzTestFiles)',
    )
    parser.add_argument(
        'verilator_src_path',
        default='/verilator/src',
        nargs='?',
        help='Path to Verilator source code (default: /verilator/src)',
    )

    args = parser.parse_args()
    # print(args.test_path, args.verilator_src_path)

    main(args.test_path, args.verilator_src_path)
