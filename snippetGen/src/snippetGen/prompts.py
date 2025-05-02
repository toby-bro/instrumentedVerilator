# ruff: noqa: E501
from typing import Optional


class PromptManager:
    """Manages prompts for generating Verilator-exercising SystemVerilog code based on target C++ file content."""

    def __init__(self) -> None:
        """Initializes the PromptManager."""
        self._system_prompt_template: Optional[str] = None
        self._initial_prompt_template: Optional[str] = None
        self._feedback_prompt_template: Optional[str] = None
        self._load_prompts()

    def _load_prompts(self) -> None:
        """Loads the prompt templates."""
        # System Prompt - Updated to mention target C++ file
        self._system_prompt_template = """You are an expert SystemVerilog designer. Your task is to generate a single, self-contained SystemVerilog file.
The goal is to include SystemVerilog language constructs that are likely to maximize code coverage within a specific target C++ file ('{target_cpp_filename}') from the Verilator codebase when Verilator processes the generated SystemVerilog. You will be shown the content of this C++ file.
Focus on generating diverse SystemVerilog declarations, assignments, operators, control flow, tasks, functions, and generate blocks that correspond to the logic and structures present in the target C++ code.
The generated SystemVerilog code MUST be syntactically correct and pass `verilator --lint-only -Wall --no-timing`.
Do NOT include:
- Simulation stimulus (like `initial` blocks driving signals over time or containing delays).
- Timing delays (`#`).
- Simulation control tasks (`$finish`, `$stop`, etc.).
- Display or monitoring tasks (`$display`, `$monitor`, `$write`, etc.).
- Module instantiations.
- Code intended for actual simulation execution logic.
Provide only the complete SystemVerilog code within a single module definition. Do not include explanations or markdown formatting."""

        # Initial Prompt - Updated to include target C++ content
        self._initial_prompt_template = """Generate a single SystemVerilog file containing one module named 'top'. This module should include a diverse set of language constructs specifically chosen to exercise the code paths within the target C++ file '{target_cpp_filename}' (content provided below) when processed by Verilator.
Analyze the C++ code to understand the Verilog constructs it handles (e.g., types of assignments, operators, control structures, data types). Generate SystemVerilog code that uses these specific constructs in various ways.
Include various data types (logic, bit, int, arrays, structs, etc.), parameters, assignments (assign, blocking=, non-blocking<=), operators, conditional statements (if/else, case), loops (for, while, etc. in `always_comb`, `always_ff`), tasks, functions, and generate blocks, prioritizing those relevant to the C++ code.
Ensure the SystemVerilog code is self-contained (no module instantiations) and syntactically correct.
Avoid simulation-specific constructs (initial blocks for stimulus, delays, $finish, $display).


Content of target C++ file '{target_cpp_filename}':
```cpp
{target_cpp_content}
```

Generate only the SystemVerilog code for this single module file."""

        # Feedback Prompt - Updated to include target C++ context
        self._feedback_prompt_template = """The following SystemVerilog code was generated to exercise the Verilator C++ file '{target_cpp_filename}', but it failed linting (`verilator --lint-only -Wall --no-timing`).

Target C++ file content ('{target_cpp_filename}'):
```cpp
{target_cpp_content}
```

Faulty generated SystemVerilog code:
```systemverilog
{generated_v_code}
```

Verilator Lint Error Output (Stderr focused):
```text
{error_summary}
```

Please analyze the target C++ code, the faulty SystemVerilog code, and the lint errors. Provide a corrected version of the SystemVerilog code that fixes the lint error(s) while still aiming to include diverse language constructs relevant to the target C++ file to exercise Verilator.
Ensure the code remains self-contained within a single module and avoids simulation-specific constructs or timing delays.
Generate only the corrected SystemVerilog code."""

    # Added target_cpp_filename parameter
    def get_system_prompt(self, target_cpp_filename: str) -> str:
        """Formats and returns the system prompt."""
        if self._system_prompt_template is None:
            raise ValueError('System prompt template not loaded.')
        return self._system_prompt_template.format(target_cpp_filename=target_cpp_filename)

    # Added target_cpp_filename and target_cpp_content parameters
    def get_initial_prompt(self, target_cpp_filename: str, target_cpp_content: str) -> str:
        """Formats and returns the initial generation prompt."""
        if self._initial_prompt_template is None:
            raise ValueError('Initial prompt template not loaded.')
        return self._initial_prompt_template.format(
            target_cpp_filename=target_cpp_filename,
            target_cpp_content=target_cpp_content,
        )

    # Added target_cpp_filename and target_cpp_content parameters
    def get_feedback_prompt(
        self,
        target_cpp_filename: str,
        target_cpp_content: str,
        generated_v_code: str,
        error_summary: str,
    ) -> str:
        """Formats and returns the feedback prompt for lint error correction."""
        if self._feedback_prompt_template is None:
            raise ValueError('Feedback prompt template not loaded.')
        return self._feedback_prompt_template.format(
            target_cpp_filename=target_cpp_filename,
            target_cpp_content=target_cpp_content,
            generated_v_code=generated_v_code,
            error_summary=error_summary,
        )
