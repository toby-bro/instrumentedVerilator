import argparse
import logging
import os
import sys

from snippetGen.analyze_coverage import find_low_coverage_from_json
from snippetGen.gen_snippet import VerilogSeedGeneratorAgent

# Adjust Python path to allow importing from snippetGen.src
# Assumes gen_seed.py is in project root (e.g., instrumentedVerilator/)
# and the snippetGen package is structured as snippetGen/src/snippetGen/
script_dir = os.path.dirname(os.path.abspath(__file__))
snippet_gen_src_dir = os.path.join(script_dir, 'snippetGen', 'src')
if snippet_gen_src_dir not in sys.path:
    sys.path.insert(0, snippet_gen_src_dir)

logger = logging.getLogger(__name__)


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description='Generate SystemVerilog snippets for C++ files with low code coverage.',
    )
    parser.add_argument(
        '--fastcov-json',
        default='coverage.json',
        type=str,
        help='Path to the fastcov coverage.json file (default: coverage.json).',
    )
    parser.add_argument(
        '--threshold',
        type=float,
        default=40.0,
        help='Upper coverage threshold percentage (0-100). Files below this will be targeted (default: 40.0).',
    )
    parser.add_argument(
        '--min-threshold',
        type=float,
        default=0.0,
        help='Lower coverage threshold percentage (0-100). Files at or above this threshold (and below --threshold) will be targeted. Default: 0.0',  # noqa: E501
    )
    parser.add_argument(
        '--model',
        required=True,
        choices=['openai', 'mistral', 'gemini'],
        help='The language model to use for snippet generation.',
    )
    parser.add_argument(
        '--max-retries',
        type=int,
        default=3,
        help='Maximum number of attempts to fix linting errors for each snippet (default: 3).',
    )
    parser.add_argument(
        '--output-dir',
        required=True,
        type=str,
        help='Directory to save the generated SystemVerilog snippets.',
    )
    parser.add_argument(
        '-v',
        '--verbose',
        action='store_true',
        help='Enable verbose output (DEBUG level logging).',
    )
    return parser.parse_args()


def file_exists(file_path: str) -> bool:
    return os.path.exists(file_path)


def generate_verilog_snippets(
    args: argparse.Namespace,
    agent: VerilogSeedGeneratorAgent,
    low_coverage_files: list[tuple[str, float]],
) -> tuple[int, int]:
    successful_generations = 0
    failed_generations = 0

    for cpp_file_path_in_report, coverage_percent in low_coverage_files:
        # Paths from coverage.json might be like "/verilator/src/V3File.cpp" (absolute in report context)
        # Adjust to be relative to the project root (e.g., "verilator/src/V3File.cpp")
        # This assumes gen_seed.py is run from the root of the Verilator project,
        # or that these paths are relative from CWD after stripping leading '/'.
        target_cpp_file_path = cpp_file_path_in_report.lstrip('/')

        logger.info(
            f'\n--- Processing C++ file: {target_cpp_file_path} (Coverage: {coverage_percent:.2f}%) ---',
        )

        if not os.path.exists(target_cpp_file_path):
            logger.error(
                f"Target C++ file '{target_cpp_file_path}' (derived from report path '{cpp_file_path_in_report}') not found. Skipping.",  # noqa: E501
            )
            failed_generations += 1
            continue

        base_cpp_filename = os.path.basename(target_cpp_file_path)
        output_sv_filename = base_cpp_filename.replace('.cpp', '.sv')
        output_sv_filepath = os.path.join(args.output_dir, output_sv_filename)

        if file_exists(output_sv_filepath):
            logger.warning(
                f"Output SystemVerilog file '{output_sv_filepath}' already exists. Skipping generation for this file.",
            )
            continue

        logger.info(f"Attempting to generate Verilog snippet for '{target_cpp_file_path}' -> '{output_sv_filepath}'")

        try:
            # generate_verilog_seed handles its own internal retries and logging for the generation process
            generated_code = agent.generate_verilog_seed(
                input_cpp_file_path=target_cpp_file_path,
                output_v_file_path=output_sv_filepath,
            )
            if generated_code:
                logger.info(
                    f"Successfully generated and linted Verilog snippet for '{target_cpp_file_path}'. Saved to '{output_sv_filepath}'.",  # noqa: E501
                )
                successful_generations += 1
            else:
                logger.error(
                    f"Failed to generate a lint-clean Verilog snippet for '{target_cpp_file_path}' after {args.max_retries + 1} attempts.",  # noqa: E501
                )
                failed_generations += 1
        except Exception as e:
            logger.error(
                f"An unexpected error occurred while processing '{target_cpp_file_path}': {e}",
            )
            if args.verbose:  # Log traceback only in verbose mode for unexpected errors
                logger.debug('Traceback:', exc_info=True)
            failed_generations += 1
        logger.info(f'--- Finished processing {target_cpp_file_path} ---')
    return successful_generations, failed_generations


def validate_args(args: argparse.Namespace) -> bool:
    # Validate arguments
    if not (0.0 <= args.threshold <= 100.0):
        logger.error('Threshold must be between 0.0 and 100.0.')
        return False
    if not (0.0 <= args.min_threshold <= 100.0):
        logger.error('Min-threshold must be between 0.0 and 100.0.')
        return False
    if args.min_threshold >= args.threshold:
        logger.error('Min-threshold must be less than threshold.')
        return False

    if not os.path.exists(args.fastcov_json):
        logger.error(f'Fastcov JSON file not found: {args.fastcov_json}')
        return False

    try:
        os.makedirs(args.output_dir, exist_ok=True)
        logger.info(f'Ensured output directory exists: {args.output_dir}')
    except OSError as e:
        logger.error(f'Could not create output directory {args.output_dir}: {e}')
        return False
    return True


def main() -> None:
    args = parse_arguments()

    # Configure logging level based on the verbose flag
    log_level = logging.DEBUG if args.verbose else logging.INFO
    logging.basicConfig(
        level=log_level,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
        force=True,  # Override any previous basicConfig
    )
    # Ensure all handlers respect the new log level
    # This affects loggers from imported modules like VerilogSeedGeneratorAgent
    logging.getLogger().setLevel(log_level)
    for handler in logging.getLogger().handlers:
        handler.setLevel(log_level)

    logger.debug(f'Arguments received: {args}')

    # Validate arguments
    if not validate_args(args):
        logger.critical('Invalid arguments provided. Exiting.')
        sys.exit(1)

    # Initialize VerilogSeedGeneratorAgent
    try:
        agent = VerilogSeedGeneratorAgent(model_type=args.model, max_retries=args.max_retries)
    except ValueError as e:
        logger.critical(f'Failed to initialize VerilogSeedGeneratorAgent: {e}')
        sys.exit(1)

    # Find low coverage files
    if args.min_threshold > 0.0:
        logger.info(
            f'Analyzing coverage from {args.fastcov_json} for files with coverage between {args.min_threshold}% and {args.threshold}%...',  # noqa: E501
        )
    else:
        logger.info(f'Analyzing coverage from {args.fastcov_json} with threshold {args.threshold}%...')

    low_coverage_files = find_low_coverage_from_json(
        args.fastcov_json,
        args.threshold,
        args.min_threshold,
    )

    if not low_coverage_files:
        if args.min_threshold > 0.0:
            logger.info(
                f'No C++ files found with coverage between {args.min_threshold:.2f}% and {args.threshold:.2f}% in {args.fastcov_json}.',  # noqa: E501
            )
        else:
            logger.info(
                f'No C++ files found with coverage below {args.threshold:.2f}% in {args.fastcov_json}.',
            )
        sys.exit(0)

    if args.min_threshold > 0.0:
        logger.info(
            f'Found {len(low_coverage_files)} C++ files with coverage between {args.min_threshold:.2f}% and {args.threshold:.2f}%. '  # noqa: E501
            f'Attempting to generate Verilog snippets...',
        )
    else:
        logger.info(
            f'Found {len(low_coverage_files)} C++ files below {args.threshold:.2f}% coverage. '
            f'Attempting to generate Verilog snippets...',
        )

    successful_generations, failed_generations = generate_verilog_snippets(args, agent, low_coverage_files)

    # Final summary
    logger.info('\n--- Overall Generation Summary ---')
    logger.info(f'Total C++ files targeted (below threshold): {len(low_coverage_files)}')
    logger.info(f'Successfully generated Verilog snippets: {successful_generations}')
    logger.info(f'Failed to generate Verilog snippets: {failed_generations}')
    logger.info('----------------------------------')

    if failed_generations > 0 or (successful_generations == 0 and low_coverage_files):
        logger.warning('Completed with one or more failures or no successful generations for targeted files.')
        sys.exit(1)
    elif not low_coverage_files:  # Should have exited earlier, but as a safeguard
        logger.info('No files were targeted for generation.')
        sys.exit(0)
    else:
        logger.info('All targeted files processed successfully.')
        sys.exit(0)


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        # Catch any unhandled exceptions from main() itself, though most should be handled within.
        logger.critical(f'A critical error occurred in the main execution: {e}')
        logger.debug('Critical Traceback:', exc_info=True)
        sys.exit(1)
