# ruff: noqa: E501
from typing import Optional


class PromptManager:
    """Manages prompts for generating Verilator-exercising SystemVerilog code snippets based on target C++ file content."""

    def __init__(self) -> None:
        """Initializes the PromptManager."""
        self._system_prompt_template: Optional[str] = None
        self._initial_prompt_template: Optional[str] = None
        self._feedback_prompt_template: Optional[str] = None
        self._load_prompts()

    def _load_prompts(self) -> None:
        """Loads the prompt templates."""
        # System Prompt - Updated for multiple snippets, GGG prefix, ports, //INJECT
        self._system_prompt_template = """You are an expert SystemVerilog designer. Your task is to generate a single SystemVerilog file containing MULTIPLE, SMALL, self-contained SystemVerilog modules (snippets).
The goal is to create diverse snippets, each targeting a specific SystemVerilog language construct likely to exercise code paths within a target C++ file ('{target_cpp_filename}') from the Verilator codebase. You will be shown the content of this C++ file.
Exactly ONE module MUST be named 'top'. Other modules should have distinct, descriptive names reflecting the construct they target.
CRITICAL REQUIREMENTS FOR EACH MODULE:
1.  All variable, parameter, port, task, function, and generate block names MUST start with the prefix 'GGG'.
2.  Each module MUST have at least one input port named 'GGGin' (you can choose width/type) and at least one output port named 'GGGout' (you can choose width/type).
3.  Include the comment '//INJECT' on its own line in places within the module logic (e.g., inside always blocks, assigns, task/function bodies) where randomly generated Verilog code could potentially be inserted by a fuzzer later. Add at least one '//INJECT' comment per module if possible.
Focus on generating diverse SystemVerilog declarations, assignments, operators, control flow, tasks, functions, and generate blocks that correspond to the logic and structures present in the target C++ code.
The generated SystemVerilog code MUST be syntactically correct and pass `verilator --lint-only -Wall --top-module top --no-timing`.
Do NOT include:
- Simulation stimulus (like `initial` blocks driving signals over time or containing delays).
- Timing delays (`#`).
- Simulation control tasks (`$finish`, `$stop`, etc.).
- Display or monitoring tasks (`$display`, `$monitor`, `$write`, etc.).
- Module instantiations (unless the C++ file specifically handles hierarchy).
Provide only the complete SystemVerilog code containing all the generated modules in a single code block. Do not include explanations or markdown formatting."""

        # Initial Prompt - Updated for multiple snippets, GGG prefix, ports, //INJECT
        self._initial_prompt_template = """Generate a single SystemVerilog file containing MULTIPLE, SMALL, self-contained modules (snippets). Exactly ONE module must be named 'top'.
Each module should target a specific language construct relevant to the Verilator C++ file '{target_cpp_filename}' (content provided below).
Analyze the C++ code to understand the Verilog constructs it handles. Generate simple SystemVerilog snippets using these constructs.
CRITICAL REQUIREMENTS FOR EACH MODULE:
1.  All identifiers (variables, parameters, ports, tasks, functions, generate blocks) MUST start with 'GGG'.
2.  Each module MUST have at least one input 'GGGin' and one output 'GGGout'.
3.  Include '//INJECT' comments where fuzzer code could be inserted. Aim for at least one per module.
Include various data types (logic, bit, int, arrays, structs, etc.), parameters, assignments (assign, blocking=, non-blocking<=), operators, conditional statements (if/else, case), loops (for, while, etc. in `always_comb`, `always_ff`), tasks, functions, and generate blocks, prioritizing those relevant to the C++ code, each within its own small module.
Ensure the SystemVerilog code is self-contained (minimal/no instantiations) and syntactically correct.
Avoid simulation-specific constructs (initial blocks for stimulus, delays, $finish, $display).


Content of target C++ file '{target_cpp_filename}':
```cpp
{target_cpp_content}
```

Generate only the SystemVerilog code containing all modules for this single file."""

        # Feedback Prompt - Updated to reinforce snippet requirements
        self._feedback_prompt_template = """The following SystemVerilog code was generated to exercise the Verilator C++ file '{target_cpp_filename}', but it failed linting (`verilator --lint-only -Wall --top-module top --no-timing`). The goal was to generate MULTIPLE small modules (snippets), one named 'top', each targeting a specific construct, with all identifiers prefixed by 'GGG', each module having 'GGGin'/'GGGout' ports, and including '//INJECT' comments.

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

Please analyze the target C++ code, the faulty SystemVerilog code, and the lint errors. Provide a corrected version of the SystemVerilog code that fixes the lint error(s) while adhering strictly to ALL the requirements:
1.  Multiple small modules, exactly one named 'top'.
2.  Each module targets a specific construct relevant to the C++ file.
3.  ALL identifiers (variables, ports, parameters, etc.) MUST start with 'GGG'.
4.  EACH module MUST have at least one input 'GGGin' and one output 'GGGout'.
5.  Include '//INJECT' comments in suitable locations within EACH module.
Ensure the code remains self-contained within the single file and avoids simulation-specific constructs or timing delays.
Generate only the corrected SystemVerilog code containing all modules."""

    def get_system_prompt(self, target_cpp_filename: str) -> str:
        """Formats and returns the system prompt."""
        if self._system_prompt_template is None:
            raise ValueError('System prompt template not loaded.')
        return self._system_prompt_template.format(target_cpp_filename=target_cpp_filename)

    def get_initial_prompt(self, target_cpp_filename: str, target_cpp_content: str) -> str:
        """Formats and returns the initial generation prompt."""
        if self._initial_prompt_template is None:
            raise ValueError('Initial prompt template not loaded.')
        return self._initial_prompt_template.format(
            target_cpp_filename=target_cpp_filename,
            target_cpp_content=target_cpp_content,
        )

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
