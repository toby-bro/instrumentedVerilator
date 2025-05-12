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
        self._system_prompt_template = """You are an expert SystemVerilog designer. Your task is to generate a single SystemVerilog file containing MULTIPLE, SMALL, self-contained executable SystemVerilog modules (snippets).
The goal is to create diverse snippets, each targeting a specific SystemVerilog language construct likely to exercise code paths within a target C++ file ('{target_cpp_filename}') from the Verilator codebase. You will be shown the content of this C++ file. All modules should have distinct, descriptive names reflecting the construct they target.
CRITICAL REQUIREMENTS FOR EACH MODULE:
1.  Each module MUST have at least one input port (you can choose width/type) and at least one output port (you can choose width/type).
2.  Include the comment '//INJECT' on its own line in places within the module logic (e.g., inside always blocks, assigns, task/function bodies) where randomly generated Verilog code could potentially be inserted by a fuzzer later. Add at least one '//INJECT' comment per module if possible.
3. All class instanciations, must be done in a procedural blocks.
4. Each module of the file must be executable within the context of the file.
Focus on generating diverse SystemVerilog declarations, assignments, operators, control flow, tasks, functions, and generate blocks that correspond to the logic and structures present in the target C++ code.
The generated SystemVerilog code MUST be syntactically correct and pass `verilator --lint-only -Wall --no-timing`.
Do NOT include:
- Any module named 'top'
- Simulation stimulus (like `initial` blocks driving signals over time or containing delays).
- Timing delays (`#`).
- Simulation control tasks (`$finish`, `$stop`, etc.).
- Display or monitoring tasks (`$display`, `$monitor`, `$write`, etc.).
- Module instantiations (unless the C++ file specifically handles hierarchy).
- Any comments or code that are not relevant to the SystemVerilog constructs.
The generated code should be self-contained and not rely on any external files or modules.
Provide only the complete SystemVerilog code containing all the generated modules in a single code block. Do not include explanations or markdown formatting."""

        # Initial Prompt - Updated for multiple snippets, GGG prefix, ports, //INJECT
        self._initial_prompt_template = """FIRST identify all the different SystemVerilog features this file is supposed to handle or simulate. THEN Once you identified all the features, that are specific to this file then generate a single SystemVerilog file containing MULTIPLE, SMALL, self-contained modules (snippets).
Each module should target a specific language construct relevant to the Verilator C++ file '{target_cpp_filename}' (content provided below).
Analyze the C++ code to understand the Verilog constructs it handles. Generate simple SystemVerilog snippets using these constructs.
CRITICAL REQUIREMENTS FOR EACH MODULE:
1.  Each module MUST have at least one input and one output.
2.  Include '//INJECT' comments where fuzzer code could be inserted. Aim for at least one per module.
3.  Each module must be executable within the file context.
4.  If you have no idea how to correct the error, delete the line that is problematic.
Include as many DIFFERENT modules as possible, each focusing on a different feature this C++ file is supposed to handle.
Ensure the SystemVerilog code is self-contained (minimal/no instantiations) and syntactically correct.
Avoid simulation-specific constructs (initial blocks for stimulus, delays, $finish, $display).


Content of target C++ file '{target_cpp_filename}':
```cpp
{target_cpp_content}
```

Generate only the SystemVerilog code containing all modules for this single file."""

        # Feedback Prompt - Updated to reinforce snippet requirements
        self._feedback_prompt_template = """The following SystemVerilog code was generated to exercise the Verilator C++ file '{target_cpp_filename}', but it failed linting (`verilator --lint-only -Wall --no-timing`). The goal was to generate MULTIPLE small modules (snippets), each targeting a specific construct, each module having an input and an output port, and including '//INJECT' comments.

Target C++ file content ('{target_cpp_filename}'):

Faulty generated SystemVerilog code:
```systemverilog
{generated_v_code}
```

Verilator Lint Error Output (Stderr focused):
```text
{error_summary}
```

Please analyze the faulty SystemVerilog code, and the lint errors. Provide a corrected version of the SystemVerilog code that fixes the lint error(s) while adhering strictly to ALL the requirements:
1.  Each module targets a specific construct relevant to the C++ file, try not to simplify too much the code.
2.  EACH module MUST have at least one input and one output.
3.  Include '//INJECT' comments in suitable locations within EACH module.
4.  No comments except for the '//INJECT' comments.
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
            # target_cpp_content=target_cpp_content,
            generated_v_code=generated_v_code,
            error_summary=error_summary,
        )
