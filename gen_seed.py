import argparse
import json
import logging
import os
import re
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
        description='Generate SystemVerilog snippets for C++ files or functions with low code coverage.',
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
        '--target',
        choices=['file', 'function'],
        default='file',
        help='Target for snippet generation: "file" for low-coverage files, "function" for zero-coverage functions (default: file).',
    )
    parser.add_argument(
        '-v',
        '--verbose',
        action='store_true',
        help='Enable verbose output (DEBUG level logging).',
    )
    return parser.parse_args()


def get_file_content(file_path: str) -> str | None:
    """Reads the entire content of a file."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            return f.read()
    except FileNotFoundError:
        logger.error(f'File not found: {file_path}')
        return None
    except Exception as e:
        logger.error(f'Error reading file {file_path}: {e}')
        return None


def extract_function_code(file_content: str, start_line: int) -> str | None:
    """
    Extracts the code for a function from file content based on start line and indentation.
    This version only uses indentation to determine the function's extent.
    """
    lines = file_content.splitlines()
    if start_line < 1 or start_line > len(lines):
        return None

    start_index = start_line - 1
    start_line_text = lines[start_index]
    match = re.match(r'^(\s*)', start_line_text)
    if not match:
        return None
    base_indent = len(match.group(1))

    extracted_lines = [start_line_text]
    for i in range(start_index + 1, len(lines)):
        line = lines[i]
        # Get indentation of the current line
        match = re.match(r'^(\s*)', line)
        indent = len(match.group(1)) if match else 0
        # Stop if indentation is less than base_indent and line is not empty
        if indent < base_indent and line.strip() != '':
            break
        extracted_lines.append(line)
    return '\n'.join(extracted_lines)


def sanitize_filename(name: str) -> str:
    """Sanitizes a string to be used as a filename."""
    # Replace characters that are not letters, numbers, underscores, or hyphens with underscores
    s = re.sub(r'[^\w\s-]', '_', name)
    # Replace whitespace with underscores
    s = re.sub(r'\s+', '_', s)
    # Remove leading/trailing whitespace
    s = s.strip()
    # Truncate if too long (optional, but good practice)
    if len(s) > 100:
        s = s[:100]
    return s


def generate_verilog_snippets_for_low_covered_functions(
    args: argparse.Namespace,
    agent: VerilogSeedGeneratorAgent,
    coverage_data: dict,
) -> tuple[int, int]:
    successful_generations = 0
    failed_generations = 0

    logger.info('Analyzing coverage data for zero-coverage functions...')

    targeted_functions = []
    for cpp_file_path_in_report, _coverage_info in coverage_data.get('sources', {}).items():
        # Map the path from the report to the actual file path in the workspace
        # If the path starts with '/slang/', map to './slang/' (relative path)
        if cpp_file_path_in_report.startswith('/slang/'):
            relative_path_from_slang_root = cpp_file_path_in_report.removeprefix('/slang/')
            target_cpp_file_path = os.path.join('slang', relative_path_from_slang_root)
        elif cpp_file_path_in_report.startswith('/verilator/'):
            relative_path_from_verilator_root = cpp_file_path_in_report.removeprefix('/verilator/')
            target_cpp_file_path = os.path.join('verilator', relative_path_from_verilator_root)
        else:
            # Handle other potential paths in the coverage report if necessary
            logger.warning(f'Unexpected file path format in coverage report: {cpp_file_path_in_report}. Skipping.')
            continue

        if not os.path.exists(target_cpp_file_path):
            print(f'File not found: {target_cpp_file_path}')
            logger.error(
                f"Target C++ file '{target_cpp_file_path}' (derived from report path '{cpp_file_path_in_report}') not found. Skipping.",  # noqa: E501
            )
            continue

        for function_name, function_coverage_info in _coverage_info[''].get('functions', {}).items():
            if function_coverage_info['execution_count'] == 0:
                targeted_functions.append((target_cpp_file_path, function_name, function_coverage_info['start_line']))

    if not targeted_functions:
        logger.info('No zero-coverage functions found in the coverage report.')
        return 0, 0

    logger.info(f'Found {len(targeted_functions)} zero-coverage functions. Attempting to generate Verilog snippets...')

    for target_cpp_file_path, function_name, start_line in targeted_functions:
        logger.info(
            f'\n--- Processing function: {function_name} in {target_cpp_file_path} ---',
        )

        file_content = get_file_content(target_cpp_file_path)
        if file_content is None:
            print(f'Failed to read file content from {target_cpp_file_path}.')
            failed_generations += len(
                _coverage_info.get("''", {}).get('functions', {}),
            )  # Count all functions in this file as failed if file read fails
            continue

        # Extract the function code based on the found line number
        function_code_snippet = extract_function_code(file_content, start_line)

        if function_code_snippet is None:
            logger.error(
                f"Failed to extract code snippet for function '{function_name}' in '{target_cpp_file_path}'. Skipping.",
            )
            failed_generations += 1
            continue

        # Sanitize function name for filename
        sanitized_function_name = sanitize_filename(function_name)
        base_cpp_filename = os.path.basename(target_cpp_file_path).replace('.cpp', '')
        output_sv_filename = f'{base_cpp_filename}_{sanitized_function_name}.sv'
        output_sv_filepath = os.path.join(args.output_dir, output_sv_filename)

        logger.info(f"Attempting to generate Verilog snippet for function '{function_name}' -> '{output_sv_filepath}'")

        try:
            # Call the agent's method, passing the temp snippet file path and the original file path for context
            # Assuming generate_verilog_seed can handle a snippet file and original file context.
            # This might require changes in the agent's implementation which I cannot make.
            # A more realistic approach with current tools might be to pass the original file path
            # and the function name/line number to the agent, and let the agent read/extract.
            # However, the prompt asks me to make a *new function* here that does the splitting/extraction.
            # This implies the extraction logic should be in this script.
            # Let's stick to the plan of writing to a temp file and passing its path, assuming the agent
            # can handle a snippet file path and the original file path for context. This seems more aligned
            # with using existing tools without modifying the agent class definition in this turn.
            # I will write the extracted snippet to a temporary file and pass that temporary file path
            # to the existing `agent.generate_verilog_seed` method. This might confuse the agent if it expects
            # a full C++ file, but it's the most direct way to use the extracted snippet with the current agent interface.
            # I will also pass the original file path as context if the agent method signature allowed it, but it doesn't.
            # So, I'll just pass the temp snippet file path.

            temp_cpp_snippet_path = os.path.join(args.output_dir, f'temp_{sanitized_function_name}.cpp_snippet')
            logger.info(f'Writing extracted snippet to temporary file: {temp_cpp_snippet_path}')
            with open(temp_cpp_snippet_path, 'w', encoding='utf-8') as f:
                f.write(function_code_snippet)

            logger.info(f'Calling agent with temporary snippet file: {temp_cpp_snippet_path}')
            generated_code = agent.generate_verilog_seed(
                input_cpp_file_path=temp_cpp_snippet_path,  # Pass the temp snippet file
                output_v_file_path=output_sv_filepath,
                coverage=coverage_data,
            )

            # Clean up the temporary file
            os.remove(temp_cpp_snippet_path)
            logger.debug(f'Removed temporary file: {temp_cpp_snippet_path}')

            if generated_code:
                logger.info(
                    f"Successfully generated and linted Verilog snippet for function '{function_name}'. Saved to '{output_sv_filepath}'.",
                )
                successful_generations += 1
            else:
                logger.error(
                    f"Failed to generate a lint-clean Verilog snippet for function '{function_name}' after {args.max_retries + 1} attempts.",
                )
                failed_generations += 1
        except Exception as e:
            logger.error(
                f"An unexpected error occurred while processing '{target_cpp_file_path}': {e}",
            )
            if args.verbose:
                logger.debug('Traceback:', exc_info=True)
            failed_generations += 1
        logger.info(f'--- Finished processing function {function_name} ---')

    return successful_generations, failed_generations


def generate_verilog_snippets_for_low_percent_files(
    args: argparse.Namespace,
    agent: VerilogSeedGeneratorAgent,
    low_coverage_files: list[tuple[str, float, dict]],
) -> tuple[int, int]:
    successful_generations = 0
    failed_generations = 0
    project_root = script_dir  # Assuming gen_seed.py is in the project root

    for cpp_file_path_in_report, coverage_percent, coverage_details in low_coverage_files:
        # Paths from coverage.json might be like "/verilator/src/V3File.cpp" (absolute in report context)
        # Adjust to be relative to the project root (e.g., "verilator/src/V3File.cpp")
        # This assumes gen_seed.py is run from the root of the Verilator project,
        # or that these paths are relative from CWD after stripping leading '/'.
        # Let's refine the path mapping based on the workspace structure provided earlier.
        # The JSON path /slang/source/... corresponds to /home/jns/Documents/Berkeley/instrumentedVerilator/yosys-slang/third_party/slang/source/...
        # So, we need to remove the leading '/slang/' and join with the base path.
        if cpp_file_path_in_report.startswith('/slang/'):
            relative_path_from_slang_root = cpp_file_path_in_report.removeprefix('/slang/')
            target_cpp_file_path = os.path.join(
                project_root,
                'yosys-slang',
                'third_party',
                'slang',
                relative_path_from_slang_root,
            )
        elif cpp_file_path_in_report.startswith('/verilator/'):
            relative_path_from_verilator_root = cpp_file_path_in_report.removeprefix('/verilator/')
            target_cpp_file_path = os.path.join('verilator', relative_path_from_verilator_root)
        else:
            # Handle other potential paths in the coverage report if necessary
            logger.warning(f'Unexpected file path format in coverage report: {cpp_file_path_in_report}. Skipping.')
            failed_generations += 1
            continue

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

        logger.info(f"Attempting to generate Verilog snippet for '{target_cpp_file_path}' -> '{output_sv_filepath}'")

        try:
            # generate_verilog_seed handles its own internal retries and logging for the generation process
            generated_code = agent.generate_verilog_seed(
                input_cpp_file_path=target_cpp_file_path,
                output_v_file_path=output_sv_filepath,
                coverage=coverage_details,
            )
            if generated_code:
                logger.info(
                    f"Successfully generated and linted Verilog snippet for '{target_cpp_file_path}'. Saved to '{output_sv_filepath}'.",
                )
                successful_generations += 1
            else:
                logger.error(
                    f"Failed to generate a lint-clean Verilog snippet for '{target_cpp_file_path}' after {args.max_retries + 1} attempts.",
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

    # Load coverage data
    try:
        with open(args.fastcov_json, 'r', encoding='utf-8') as f:
            coverage_data = json.load(f)
    except FileNotFoundError:
        logger.critical(f'Coverage JSON file not found: {args.fastcov_json}')
        sys.exit(1)
    except json.JSONDecodeError:
        logger.critical(f'Error decoding JSON from {args.fastcov_json}. Is it a valid JSON file?')
        sys.exit(1)
    except Exception as e:
        logger.critical(f'An error occurred while reading {args.fastcov_json}: {e}')
        sys.exit(1)

    successful_generations = 0
    failed_generations = 0

    if args.target == 'file':
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

        successful_generations, failed_generations = generate_verilog_snippets_for_low_percent_files(
            args,
            agent,
            low_coverage_files,
        )

    elif args.target == 'function':
        successful_generations, failed_generations = generate_verilog_snippets_for_low_covered_functions(
            args,
            agent,
            coverage_data,
        )

    # Final summary
    logger.info('\n--- Overall Generation Summary ---')
    if args.target == 'file':
        logger.info(f'Total C++ files targeted (below threshold): {len(low_coverage_files)}')
    elif args.target == 'function':
        # Recalculate total targeted functions as some might have been skipped due to file errors
        total_targeted_functions = 0
        for cpp_file_path_in_report, coverage_info in coverage_data.get('sources', {}).items():
            if cpp_file_path_in_report.startswith('/slang/'):  # Only consider slang files for now
                target_cpp_file_path = os.path.join(
                    script_dir,
                    'yosys-slang',
                    'third_party',
                    'slang',
                    cpp_file_path_in_report.removeprefix('/slang/'),
                )
                if os.path.exists(target_cpp_file_path):
                    for function_name, function_coverage_info in coverage_info.get('functions', {}).items():
                        if function_coverage_info.get('execution_count', 0) == 0:
                            total_targeted_functions += 1
        logger.info(f'Total zero-coverage functions targeted: {total_targeted_functions}')

    logger.info(f'Successfully generated Verilog snippets: {successful_generations}')
    logger.info(f'Failed to generate Verilog snippets: {failed_generations}')
    logger.info('----------------------------------')

    if failed_generations > 0 or (
        successful_generations == 0
        and (len(low_coverage_files) > 0 if args.target == 'file' else total_targeted_functions > 0)
    ):
        logger.warning('Completed with one or more failures or no successful generations for targeted items.')
        sys.exit(1)
    elif (args.target == 'file' and not low_coverage_files) or (
        args.target == 'function' and total_targeted_functions == 0
    ):
        logger.info('No items were targeted for generation.')
        sys.exit(0)
    else:
        logger.info('All targeted items processed successfully.')
        sys.exit(0)


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        # Catch any unhandled exceptions from main() itself, though most should be handled within.
        logger.critical(f'A critical error occurred in the main execution: {e}')
        logger.debug('Critical Traceback:', exc_info=True)
        sys.exit(1)
