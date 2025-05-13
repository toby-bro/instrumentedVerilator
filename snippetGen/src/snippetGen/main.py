import argparse
import logging
import os
from typing import Literal, Optional

from snippetGen.code_executor import CodeExecutor
from snippetGen.llm_handler import LLMHandler
from snippetGen.prompts import PromptManager

logging.basicConfig(level=logging.INFO, format='%(levelname)s - %(message)s')
logger = logging.getLogger(__name__)


class VerilogSeedGeneratorAgent:
    """
    Generates and refines self-contained SystemVerilog code aimed at exercising
    a target C++ file within the Verilator tool, ensuring the code is lint-clean.
    """

    def __init__(self, model_type: Literal['openai', 'mistral', 'gemini'], max_retries: int = 3) -> None:
        """
        Initializes the VerilogSeedGeneratorAgent.

        Args:
            model_type: The type of language model to use.
            max_retries: Maximum number of attempts to fix linting errors.
        """
        try:
            self.llm_handler = LLMHandler(model_type=model_type)
        except ValueError as e:
            raise ValueError(f'Failed to initialize LLMHandler: {e}') from e

        self.code_executor = CodeExecutor()
        self.prompt_manager = PromptManager()
        self.max_retries = max_retries

        logger.debug(f'Max retries for fixing lint errors: {self.max_retries}')

    def _read_file(self, file_path: str) -> str:
        """Reads the content of the specified file."""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                return f.read()
        except FileNotFoundError:
            logger.error(f'File not found at {file_path}')
            raise
        except Exception as e:
            logger.error(f'Error reading file {file_path}: {e}')
            raise IOError(f'Could not read file: {file_path}') from e

    def generate_verilog_seed(self, input_cpp_file_path: str, output_v_file_path: str) -> Optional[str]:
        """
        Generates and refines SystemVerilog code until it passes Verilator linting,
        guided by the content of the target C++ file.

        Args:
            input_cpp_file_path: Path to the target C++ file from Verilator codebase.
            output_v_file_path: Path where the generated SystemVerilog (.sv/.v) will be saved.

        Returns:
            The successfully linted SystemVerilog code as a string,
            or None if it fails after retries.
        """

        try:
            target_cpp_content = self._read_file(input_cpp_file_path)
            target_cpp_filename = os.path.basename(input_cpp_file_path)
        except (FileNotFoundError, IOError):
            logger.error(f'Failed to read target C++ file: {input_cpp_file_path}')
            return None

        system_prompt = self.prompt_manager.get_system_prompt(target_cpp_filename=target_cpp_filename)
        initial_prompt = self.prompt_manager.get_initial_prompt(
            target_cpp_filename=target_cpp_filename,
            target_cpp_content=target_cpp_content,
        )

        generated_v_code = ''
        current_prompt = initial_prompt

        for attempt in range(self.max_retries + 1):
            logger.info(f'--- Attempt {attempt + 1} of {self.max_retries + 1} ---')

            try:
                logger.info('Requesting SystemVerilog code from LLM...')
                generated_v_code = self.llm_handler.invoke_llm(current_prompt, system_prompt)

                if not generated_v_code.strip():
                    logger.warning('LLM returned empty code. Retrying with initial prompt.')
                    current_prompt = initial_prompt
                    continue

                self.code_executor.write_code(output_v_file_path, generated_v_code)

                lint_success, lint_stdout, lint_stderr = self.code_executor.lint_verilog(
                    generated_v_path=output_v_file_path,
                )

                if lint_success:
                    logger.info('Verilator linting passed.')
                    lint_success, lint_stdout, lint_stderr = self.code_executor.simulate_verilog(
                        generated_v_path=output_v_file_path,
                    )

                if lint_success:
                    logger.info(
                        f'Successfully generated and linted SystemVerilog code: {output_v_file_path}',
                    )
                    return generated_v_code

                error_summary = f'Verilator Linting failed.\nStderr:\n{lint_stderr.strip()}'
                logger.error(f'Linting Error details:\n{error_summary}')

                if attempt < self.max_retries:
                    logger.info('Attempting to fix the lint error...')
                    current_prompt = self.prompt_manager.get_feedback_prompt(
                        target_cpp_filename=target_cpp_filename,
                        target_cpp_content=target_cpp_content,
                        generated_v_code=generated_v_code,
                        error_summary=lint_stderr.strip(),
                    )
                else:
                    logger.error(
                        'Maximum retries reached. Failed to generate lint-clean SystemVerilog code.',
                    )
                    return None

            except (IOError, RuntimeError, ValueError) as e:
                logger.error(f'An error occurred during attempt {attempt + 1}: {e}')
                if attempt < self.max_retries:
                    logger.info('Retrying generation...')
                    current_prompt = initial_prompt
                else:
                    logger.error('Failed due to error after maximum retries.')
                    return None
            except Exception as e:
                logger.error(f'An unexpected error occurred during attempt {attempt + 1}: {e}')
                if attempt < self.max_retries:
                    logger.info('Retrying generation...')
                    current_prompt = initial_prompt
                else:
                    logger.error('Failed due to unexpected error after maximum retries.')
                    return None

        logger.error('Failed to generate lint-clean SystemVerilog code after all attempts.')
        return None


if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        description='Generate lint-clean SystemVerilog code to exercise Verilator C++ files using an LLM.',
    )
    parser.add_argument(
        '--model',
        required=True,
        choices=['openai', 'mistral', 'gemini'],
        help='The language model to use.',
    )
    parser.add_argument(
        '--target',
        required=True,
        help='The path to the target C++ file within the Verilator codebase to maximize coverage for.',
    )
    parser.add_argument(
        '--output',
        required=True,
        help='The path where the generated SystemVerilog code will be saved (e.g., generated_constructs.sv).',
    )
    parser.add_argument(
        '--max-retries',
        type=int,
        default=3,
        help='Maximum number of attempts to fix linting errors (default: 3).',
    )
    # Add the verbose argument
    parser.add_argument(
        '-v',
        '--verbose',
        action='store_true',  # Sets args.verbose to True if flag is present
        help='Enable verbose output (DEBUG level logging).',
    )
    args = parser.parse_args()

    # Reconfigure logging level based on the verbose flag
    log_level = logging.DEBUG if args.verbose else logging.INFO
    # Get the root logger and set its level
    # Also update the handler level if using basicConfig's default handler
    logging.getLogger().setLevel(log_level)
    for handler in logging.getLogger().handlers:
        handler.setLevel(log_level)

    # Now logger.debug messages will be shown if -v is used
    logger.debug(f'Arguments received: {args}')

    if not args.output.endswith(('.v', '.sv')):
        logger.warning('Output file does not end with .v or .sv. It will be treated as a SystemVerilog source file.')
    if not os.path.exists(args.target):
        logger.error(f'Target C++ file not found: {args.target}. Cannot generate SystemVerilog.')
        exit(1)
    if os.path.abspath(args.target) == os.path.abspath(args.output):
        logger.error('Target C++ file and output SystemVerilog file cannot be the same.')
        exit(1)

    try:
        agent = VerilogSeedGeneratorAgent(model_type=args.model, max_retries=args.max_retries)
        successful_code = agent.generate_verilog_seed(
            input_cpp_file_path=args.target,
            output_v_file_path=args.output,
        )

        if successful_code:
            logger.info('--- Successfully Generated and Linted SystemVerilog Code ---')
            logger.info(f'Final lint-clean SystemVerilog code saved to: {args.output}')
            logger.info('-------------------------------------------------------------')
            exit(0)
        else:
            logger.error('--- Failed to Generate Lint-Clean SystemVerilog Code ---')
            logger.error(f'Check logs and the last generated file: {args.output}')
            logger.error('---------------------------------------')
            exit(1)

    except (ValueError, FileNotFoundError, IOError, RuntimeError) as e:
        logger.critical(f'Process failed critically: {e}')
        exit(1)
    except Exception as e:
        # Log traceback at debug level for critical errors too
        logger.debug('Critical Traceback:', exc_info=True)
        logger.critical(f'An unexpected critical error occurred: {e}')
        exit(1)
