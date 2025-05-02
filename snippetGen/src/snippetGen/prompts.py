# ruff: noqa: E501
from typing import Optional


class PromptManager:
    """Manages and formats prompts for Verilog testbench generation."""

    def __init__(self) -> None:
        """Initializes the PromptManager."""
        # In a more complex scenario, this could load from a JSON/YAML file.
        # For now, templates are stored directly.
        self._system_prompt_template: Optional[str] = None
        self._initial_prompt_template: Optional[str] = None
        self._feedback_prompt_template: Optional[str] = None
        self._load_prompts()  # Load prompts on initialization

    def _load_prompts(self) -> None:
        """Loads the prompt templates."""
        # System Prompt
        self._system_prompt_template = """You are an expert Verilog designer. Your task is to write a Verilog testbench module that instantiates and stimulates a given Verilog module ('{target_filename}', assumed top module name '{top_module_guess}').
The goal is to create a testbench that, when compiled and simulated with the target module using Verilator, runs without compilation errors and simulation runtime errors (e.g., assertion failures, crashes).
The testbench should include stimulus generation (e.g., driving inputs like clk, reset, and others) and potentially basic checks or `$display` statements. It should use `$finish;` to end the simulation gracefully.
Provide only the complete Verilog code for the testbench module. Do not include explanations, comments about the code itself, or markdown formatting.
Assume the testbench will be compiled with '{target_filename}' and driven by a standard C++ main file (like sim_main.cpp used with Verilator's --exe option)."""

        # Initial Prompt
        self._initial_prompt_template = """Write a complete Verilog testbench module (e.g., `module {top_module_guess}_tb; ... endmodule`) for the Verilog module defined in '{target_filename}'.
The testbench should instantiate the module '{top_module_guess}' (e.g., `{top_module_guess} dut (...);`).
It must drive necessary inputs, especially `clk` and `reset` if they exist. Generate a clock signal and apply a reset sequence.
Provide some basic stimulus to other inputs if present.
Include `$finish;` at the end of the simulation sequence within an `initial` block.

Content of '{target_filename}':
```verilog
{original_verilog_code}
```

Generate only the Verilog code for the testbench module. Ensure it's a single, complete Verilog file."""

        # Feedback Prompt
        self._feedback_prompt_template = """The following Verilog testbench code was generated for '{target_filename}', but it failed during Verilator compilation or simulation.

Original Verilog module content ('{target_filename}'):
```verilog
{original_verilog_code}
```

Faulty generated Verilog testbench code:
```verilog
{generated_v_code}
```

Verilator Compilation/Simulation Error Output (Stderr focused):
```verilog
{error_summary}
```

Please analyze the original Verilog module, the faulty generated testbench code, and the error message.
Provide a corrected version of the generated Verilog testbench code that fixes the error and successfully compiles and simulates when linked with '{target_filename}'.
Generate only the corrected Verilog testbench code."""

    def get_system_prompt(self, target_filename: str, top_module_guess: str) -> str:
        """Formats and returns the system prompt."""
        if self._system_prompt_template is None:
            raise ValueError('System prompt template not loaded.')
        return self._system_prompt_template.format(
            target_filename=target_filename,
            top_module_guess=top_module_guess,
        )

    def get_initial_prompt(self, target_filename: str, top_module_guess: str, original_verilog_code: str) -> str:
        """Formats and returns the initial generation prompt."""
        if self._initial_prompt_template is None:
            raise ValueError('Initial prompt template not loaded.')
        return self._initial_prompt_template.format(
            target_filename=target_filename,
            top_module_guess=top_module_guess,
            original_verilog_code=original_verilog_code,
        )

    def get_feedback_prompt(
        self,
        target_filename: str,
        original_verilog_code: str,
        generated_v_code: str,
        error_summary: str,
    ) -> str:
        """Formats and returns the feedback prompt for error correction."""
        if self._feedback_prompt_template is None:
            raise ValueError('Feedback prompt template not loaded.')
        return self._feedback_prompt_template.format(
            target_filename=target_filename,
            original_verilog_code=original_verilog_code,
            generated_v_code=generated_v_code,
            error_summary=error_summary,
        )
