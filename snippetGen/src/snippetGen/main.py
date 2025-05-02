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
    Generates and refines Verilog testbench code to interact with a target Verilog module,
    compiling and simulating using Verilator, using feedback until it runs without errors.
    """

    def __init__(self, model_type: Literal['openai', 'mistral', 'gemini'], max_retries: int = 3) -> None:
        """
        Initializes the VerilogSeedGeneratorAgent.

        Args:
            model_type: The type of language model to use.
            max_retries: Maximum number of attempts to fix compilation/simulation errors.
        """
        # Initialize components
        try:
            self.llm_handler = LLMHandler(model_type=model_type)
        except ValueError as e:
            raise ValueError(f'Failed to initialize LLMHandler: {e}') from e

        self.code_executor = CodeExecutor()
        self.prompt_manager = PromptManager()
        self.max_retries = max_retries
        # Define path to the standard sim_main.cpp relative to this script's location
        script_dir = os.path.dirname(__file__)
        self.sim_main_cpp_path = os.path.abspath(os.path.join(script_dir, 'sim_main.cpp'))
        if not os.path.exists(self.sim_main_cpp_path):
            raise FileNotFoundError(f'Critical: sim_main.cpp not found at expected location: {self.sim_main_cpp_path}')

        # Use logger.debug for these internal setup messages
        logger.debug(f'Max retries for fixing errors: {self.max_retries}')
        logger.debug(f'Using sim_main.cpp: {self.sim_main_cpp_path}')

    def _read_file(self, file_path: str) -> str:
        """Reads the content of the specified file."""
        try:
            with open(file_path, 'r') as f:
                return f.read()
        except FileNotFoundError:
            logger.error(f'File not found at {file_path}')  # Use logger
            raise
        except Exception as e:
            logger.error(f'Error reading file {file_path}: {e}')  # Use logger
            raise IOError(f'Could not read file: {file_path}') from e

    def generate_verilog_seed(self, input_v_file_path: str, output_v_file_path: str) -> Optional[str]:
        """
        Generates, compiles, simulates, and refines Verilog testbench code.

        Args:
            input_v_file_path: Path to the target Verilog module file (.v).
            output_v_file_path: Path where the generated Verilog testbench (.v) will be saved.

        Returns:
            The successfully compiled and simulated Verilog testbench code as a string,
            or None if it fails after retries.
        """

        try:
            original_verilog_code = self._read_file(input_v_file_path)
            target_filename = os.path.basename(input_v_file_path)
            top_module_guess = self.code_executor._get_top_module_name(input_v_file_path) or 'top'

        except (FileNotFoundError, IOError):
            return None  # Error already logged in _read_file

        # --- Get prompts from PromptManager ---
        system_prompt = self.prompt_manager.get_system_prompt(
            target_filename=target_filename,
            top_module_guess=top_module_guess,
        )
        initial_prompt = self.prompt_manager.get_initial_prompt(
            target_filename=target_filename,
            top_module_guess=top_module_guess,
            original_verilog_code=original_verilog_code,
        )
        # --- Prompts loaded ---

        generated_v_code = ''
        current_prompt = initial_prompt  # Start with the initial prompt

        for attempt in range(self.max_retries + 1):
            logger.info(f'--- Attempt {attempt + 1} of {self.max_retries + 1} ---')

            try:
                # 1. Generate Verilog code
                logger.info('Requesting Verilog testbench code from LLM...')
                generated_v_code = self.llm_handler.invoke_llm(current_prompt, system_prompt)

                if not generated_v_code.strip():
                    logger.warning('LLM returned empty code. Retrying with initial prompt.')
                    current_prompt = initial_prompt
                    continue

                # 2. Write generated code to file
                self.code_executor.write_code(output_v_file_path, generated_v_code)

                # 3. Compile using Verilator
                compile_success, executable_path, compile_stdout, compile_stderr = self.code_executor.compile_verilog(
                    generated_v_path=output_v_file_path,
                    target_v_path=input_v_file_path,
                    sim_main_cpp_path=self.sim_main_cpp_path,
                )

                run_success = False
                run_stdout = ''
                run_stderr = ''

                # 4. Run simulation if compilation succeeded
                if compile_success and executable_path:
                    run_success, run_stdout, run_stderr = self.code_executor.run_simulation(executable_path)
                else:
                    # Compilation failed, run_success remains False
                    logger.error('Compilation failed, skipping simulation run.')

                # 5. Check overall result and prepare feedback
                if compile_success and run_success:
                    logger.info(
                        f'Successfully compiled and simulated generated Verilog testbench: {output_v_file_path}',
                    )
                    return generated_v_code
                # Combine outputs for feedback, prioritizing stderr
                combined_stdout = compile_stdout + '\n--- Simulation Run ---\n' + run_stdout
                combined_stderr = compile_stderr + '\n--- Simulation Run ---\n' + run_stderr
                error_summary = f'Verilator Compilation/Simulation failed.\nStderr:\n{combined_stderr.strip()}'
                # Optionally add stdout summary here if needed

                logger.error(f'Error details:\n{error_summary}')

                if attempt < self.max_retries:
                    logger.info('Attempting to fix the error...')
                    current_prompt = self.prompt_manager.get_feedback_prompt(
                        target_filename=target_filename,
                        original_verilog_code=original_verilog_code,
                        generated_v_code=generated_v_code,
                        error_summary=combined_stderr.strip(),  # Pass combined stderr
                    )
                else:
                    logger.error(
                        'Maximum retries reached. Failed to generate working Verilog testbench code.',
                    )
                    return None

            except (IOError, RuntimeError, ValueError) as e:
                # Errors from LLM invocation, file writing, or executor setup
                logger.error(f'An error occurred during attempt {attempt + 1}: {e}')  # Use logger
                if attempt < self.max_retries:
                    logger.info('Retrying generation...')  # Use logger
                    # Reset prompt to initial, as the state might be corrupted
                    current_prompt = initial_prompt  # Re-fetch initial prompt
                else:
                    logger.error('Failed due to error after maximum retries.')  # Use logger
                    return None
            except Exception as e:
                # Catch unexpected errors
                logger.error(f'An unexpected error occurred during attempt {attempt + 1}: {e}')  # Use logger
                if attempt < self.max_retries:
                    logger.info('Retrying generation...')  # Use logger
                    current_prompt = initial_prompt  # Re-fetch initial prompt
                else:
                    logger.error('Failed due to unexpected error after maximum retries.')  # Use logger
                    return None

        logger.error('Failed to generate executable Verilog testbench code after all attempts.')  # Use logger
        return None  # Should be unreachable if loop logic is correct


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Generate and execute Verilog testbench seeds using an LLM.')
    parser.add_argument(
        '--model',
        required=True,
        choices=['openai', 'mistral', 'gemini'],
        help='The language model to use.',
    )
    parser.add_argument('--file', required=True, help='The path to the target Verilog file (.v).')
    parser.add_argument(
        '--output-file',
        required=True,
        help='The path where the generated Verilog testbench code will be saved (e.g., generated_seed.v).',
    )
    parser.add_argument(
        '--max-retries',
        type=int,
        default=3,
        help='Maximum number of attempts to fix compilation/simulation errors (default: 3).',
    )
    args = parser.parse_args()

    # Basic validation
    if not args.output_file.endswith('.v'):
        logger.warning('Output file does not end with .v. It will be treated as a Verilog source file.')  # Use logger
    if os.path.abspath(args.file) == os.path.abspath(args.output_file):
        logger.error('Input file and output file cannot be the same.')  # Use logger
        exit(1)
    if not os.path.exists(args.file):
        logger.info(f'Input file not found: {args.file}. Creating an empty file.')
        try:
            # Ensure the directory exists
            file_dir = os.path.dirname(args.file)
            if file_dir:  # Only create dirs if a path is specified
                os.makedirs(file_dir, exist_ok=True)
            # Create the empty file
            with open(args.file, 'w') as f:
                pass
            logger.info(f'Successfully created empty file: {args.file}')
        except OSError as e:
            logger.error(f'Failed to create input file {args.file}: {e}')
            exit(1)  # Exit if we cannot create the file

    try:
        agent = VerilogSeedGeneratorAgent(model_type=args.model, max_retries=args.max_retries)
        successful_code = agent.generate_verilog_seed(
            input_v_file_path=args.file,
            output_v_file_path=args.output_file,
        )

        if successful_code:
            logger.info('--- Successfully Generated, Compiled, and Simulated Verilog Testbench Code ---')
            logger.info(f'Final working Verilog testbench code saved to: {args.output_file}')
            # Determine potential executable path based on obj_dir convention
            obj_dir = os.path.join(os.path.dirname(args.output_file), 'obj_dir')
            top_module = CodeExecutor()._get_top_module_name(args.file) or 'top'  # Re-guess or use default
            executable_path = os.path.join(obj_dir, f'V{top_module}')
            logger.info(f'Executable potentially located at: {executable_path}')
            logger.info('-------------------------------------------------------------')
            exit(0)
        else:
            logger.error('--- Failed to Generate Working Verilog Testbench Code ---')
            logger.error(f'Check logs and the last generated file: {args.output_file}')
            # Also mention obj_dir for debugging artifacts
            obj_dir = os.path.join(os.path.dirname(args.output_file), 'obj_dir')
            logger.error(f'Check Verilator artifacts for errors in: {obj_dir}')
            logger.error('---------------------------------------')
            exit(1)

    except (ValueError, FileNotFoundError, IOError, RuntimeError) as e:
        logger.critical(f'Process failed critically: {e}')
        exit(1)
    except Exception as e:
        logger.critical(f'An unexpected critical error occurred: {e}')
        exit(1)
