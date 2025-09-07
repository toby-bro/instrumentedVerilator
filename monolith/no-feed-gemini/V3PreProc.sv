module PreprocessorBasics #(
    parameter ENABLE_FEATURE_A = 1'b1,
    parameter ENABLE_FEATURE_B = 1'b0
) (
    input logic [7:0] input_val_pb,
    output logic [7:0] output_val_pb
);
    `define SIMPLE_MACRO_A 8'd10
    `define SIMPLE_MACRO_B 8'd20
    `define DEBUG_INFO "Debugging is on!"
    `ifdef ENABLE_FEATURE_A
        parameter MACRO_A_VALUE = `SIMPLE_MACRO_A;
        `undef SIMPLE_MACRO_A 
    `else
        parameter MACRO_A_VALUE = 8'd5;
    `endif
    `ifndef UNDEF_MACRO_C
        `define MACRO_C 8'd30
    `endif
    `ifdef NON_EXISTENT_MACRO_1
        parameter COND_VALUE_TEST = 8'd100;
    `elsif ENABLE_FEATURE_B 
        parameter COND_VALUE_TEST = 8'd200;
    `elsif NON_EXISTENT_MACRO_2 
        parameter COND_VALUE_TEST = 8'd250;
    `else
        parameter COND_VALUE_TEST = 8'd300; 
    `endif
    `endif 
    `undefineall
    `define REC_ALPHA `REC_BETA
    `define REC_BETA `REC_GAMMA
    `define REC_GAMMA 8'd255 
    parameter REC_VAL = `REC_ALPHA; 
    assign output_val_pb = MACRO_A_VALUE + `MACRO_C + COND_VALUE_TEST + REC_VAL + input_val_pb;
    class MyDesignSpecificClass;
        int config_id;
        function new(int id);
            this.config_id = id;
        endfunction
        function int get_config_id();
            return config_id;
        endfunction
    endclass
    logic [31:0] class_proc_output;
    always_comb begin
        MyDesignSpecificClass my_cfg = new(input_val_pb + 1); 
        class_proc_output = my_cfg.get_config_id(); 
    end
endmodule
module ParameterizedMacros (
    input logic [3:0] multiplier_pm,
    output logic [15:0] result_pm
);
    `define ADD_VALS(a, b) (a + b)
    parameter SUM_VAL = `ADD_VALS(10, 20);
    `define SUBTRACT_VALS(x, y=5) (x - y)
    parameter SUB_VAL1 = `SUBTRACT_VALS(10);        
    parameter SUB_VAL2 = `SUBTRACT_VALS(10, 3);     
    `define MULTIPLY_VALS(a, b) (a * b)
    `define COMPOUND_OPERATION(p1, p2, p3) `ADD_VALS(`MULTIPLY_VALS(p1, p2), p3)
    parameter NESTED_OP_VAL = `COMPOUND_OPERATION(2, 3, 4); 
    `define PAIR_VALUES(val1, val2) {val1, val2}
    parameter COMPLEX_PAIR = `PAIR_VALUES(8'hAB, `ADD_VALS(1,2));
    `define RECURSIVE_A(val) val `RECURSIVE_B
    `define RECURSIVE_B 
    parameter LOOP_SAFE_VAL = `RECURSIVE_A(1); 
    `define ZERO_VALUE_MACRO 0
    `define MACRO_WITH_ESCAPED_QUOTE `\`" 
    parameter ESCAPED_QUOTE_ACCESS = `MACRO_WITH_ESCAPED_QUOTE[0]; 
    `define MACRO_WITH_ESCAPED_NEWLINE "first line \\n second line"
    parameter ESCAPED_NL_ACCESS = `MACRO_WITH_ESCAPED_NEWLINE[0]; 
    `define EMPTY_PARAMETERIZED_MACRO(x) 
    `define CONCATENATE_WITH_EMPTY(arg) Pref``arg``Suf 
    parameter EMPTY_CONCAT_TEST_VAL = `CONCATENATE_WITH_EMPTY(`EMPTY_PARAMETERIZED_MACRO(dummy)); 
    assign result_pm = SUM_VAL + SUB_VAL1 + SUB_VAL2 + NESTED_OP_VAL + COMPLEX_PAIR[7:0] + (LOOP_SAFE_VAL == 1) +
                       ESCAPED_QUOTE_ACCESS + ESCAPED_NL_ACCESS + EMPTY_CONCAT_TEST_VAL[0] + multiplier_pm * 2;
endmodule
module MacroConcatenation (
    input logic [7:0] input_data_mc,
    output logic [15:0] output_data_mc
);
    `define PREFIX_TOKEN "LEFT_"
    `define SUFFIX_TOKEN "_RIGHT"
    `define MIDDLE_TOKEN "CENTRAL"
    `define BLANK_MACRO 
    `define ARG_TO_JOIN(arg) some_val_``arg
    `define GET_LSB(val) val[0]
    parameter JOINED_SYMBOL = `PREFIX_TOKEN``MIDDLE_TOKEN``SUFFIX_TOKEN; 
    `define VALUE_FOR_JOIN 123
    parameter MACRO_JOIN_MACRO = `VALUE_FOR_JOIN``_END; 
    parameter LITERAL_JOIN_MACRO = 456``_PREFIX; 
    parameter EMPTY_MACRO_JOIN = `PREFIX_TOKEN``BLANK_MACRO``SUFFIX_TOKEN; 
    `define PARAM_MACRO_OUT(arg_val) process_``arg_val
    parameter PARAM_IN_JOIN = `PARAM_MACRO_OUT(data)``_completed; 
    `define CONCAT_IN_DEF(p_arg1, p_arg2) `GET_LSB(p_arg1)``p_arg2
    parameter CONCAT_IN_DEFINE_RESULT = `CONCAT_IN_DEF(input_data_mc, _bit); 
    assign output_data_mc = JOINED_SYMBOL[0] + MACRO_JOIN_MACRO[0] + LITERAL_JOIN_MACRO[0] + EMPTY_MACRO_JOIN[0] +
                           PARAM_IN_JOIN[0] + CONCAT_IN_DEFINE_RESULT[0] + input_data_mc[0];
endmodule
module MacroStringification (
    input logic [7:0] value_ms,
    output logic [7:0] output_code_ms
);
    `define STRINGIFY(x) `"x`"
    `define MULTI_LINE_TEXT line one \
                             line two
    `define QUOTED_TEXT "This is an \"inner\" quote."
    `define NESTED_STRING_MACRO(y) `"Argument y: `STRINGIFY(y)`"
    `define MACRO_WITH_BACKQUOTE `BACKQUOTE_TOKEN 
    `define BACKQUOTE_TOKEN ` 
    parameter S_VAL_1 = `STRINGIFY(my_identifier); 
    parameter S_VAL_2 = `STRINGIFY(12345); 
    parameter S_VAL_3 = `STRINGIFY(`MULTI_LINE_TEXT); 
    parameter S_VAL_4 = `STRINGIFY(`QUOTED_TEXT); 
    parameter S_VAL_5 = `NESTED_STRING_MACRO(test_arg); 
    `define COMPLEX_STRING(a, b) `"Value: `a``b`"
    `define EXPAND_A 100
    `define EXPAND_B 200
    parameter S_VAL_6 = `COMPLEX_STRING(`EXPAND_A, `EXPAND_B); 
    parameter S_VAL_7 = `STRINGIFY(`BACKQUOTE_TOKEN); 
    assign output_code_ms = value_ms + S_VAL_1[0] + S_VAL_2[0] + S_VAL_3[0] + S_VAL_4[0] + S_VAL_5[0] + S_VAL_6[0] + S_VAL_7[0];
endmodule
module ConditionalExpressions (
    input logic enable_ce,
    output logic [7:0] config_value_ce
);
    `define COND_DEFINED_MACRO
    `define COND_UNDEFINED_MACRO_ZERO 0 
    `define COND_DEFINED_MACRO_ONE 1
    `define ANOTHER_COND_DEFINED_MACRO
    `ifdef (`COND_DEFINED_MACRO && !`NON_EXISTENT_MACRO_A)
        parameter PATH_A_CHOICE = 8'd10; 
    `else
        parameter PATH_A_CHOICE = 8'd20;
    `endif
    `ifdef (!`COND_DEFINED_MACRO_ONE || `NON_EXISTENT_MACRO_B) 
        parameter PATH_B_CHOICE = 8'd30;
    `elsif (`COND_UNDEFINED_MACRO_ZERO || `ANOTHER_COND_DEFINED_MACRO) 
        parameter PATH_B_CHOICE = 8'd40; 
    `else
        parameter PATH_B_CHOICE = 8'd50;
    `endif
    `define PRED_A
    `define PRED_B
    `undef PRED_C
    `undef PRED_D
    `ifdef (`PRED_A -> `PRED_B)
        parameter IMPLICATION_TEST1 = 8'd1;
    `else
        parameter IMPLICATION_TEST1 = 8'd0;
    `endif
    `ifdef (`PRED_A -> `PRED_C)
        parameter IMPLICATION_TEST2 = 8'd0; 
    `else
        parameter IMPLICATION_TEST2 = 8'd1;
    `endif
    `ifdef (`PRED_C <-> `PRED_D)
        parameter EQUIVALENCE_TEST1 = 8'd1; 
    `else
        parameter EQUIVALENCE_TEST1 = 8'd0;
    `endif
    `ifdef (`PRED_A <-> `PRED_C)
        parameter EQUIVALENCE_TEST2 = 8'd0; 
    `else
        parameter EQUIVALENCE_TEST2 = 8'd1;
    `endif
    assign config_value_ce = enable_ce ? (PATH_A_CHOICE + PATH_B_CHOICE) : (IMPLICATION_TEST1 + IMPLICATION_TEST2 + EQUIVALENCE_TEST1 + EQUIVALENCE_TEST2);
endmodule
module IncludeLineComments (
    input logic [7:0] dummy_input_ilc,
    output logic [7:0] dummy_output_ilc
);
    /* This is a multi-line comment.
       It should be parsed by the preprocessor,
       potentially triggering 'commentCleanup'. */
    /*verilator public*/ wire comment_wire_a; 
    /* verilator tracing_on */
    /* verilator full_case */ 
    /* synopsys full_case */ wire comment_wire_b; 
    /* synopsys parallel_case */ 
    /* verilator public_flat_rw @(posedge clk) */ 
    /* cadence internal */ 
    /* pragma once */ 
    /* ambit synthesis foo */ 
    `include "local_header.svh"
    `include <system_header.svh>
    `include "path/to/another/file.svh"
    `line 1000 "custom_file_A.sv" 0 
    parameter LINE_INFO_A = 1;
    `line `__LINE__ "current_module_context.sv" 1 
    parameter LINE_INFO_B = 2;
    `line reset 
    parameter LINE_INFO_C = 3;
    assign dummy_output_ilc = dummy_input_ilc + LINE_INFO_A + LINE_INFO_B + LINE_INFO_C;
endmodule
