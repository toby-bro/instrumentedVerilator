module SvPreproc_BasicDefines (
    input logic [7:0] in_val_a,
    output logic [7:0] out_result_a
);
    `define SIMPLE_CONST_A 10
    `define MY_TEXT "HelloPreproc_Basic"
    assign out_result_a = in_val_a + `SIMPLE_CONST_A;
    `undef SIMPLE_CONST_A
    `define SIMPLE_CONST_A 20
    logic [7:0] temp_b;
    assign temp_b = `SIMPLE_CONST_A;
    `undefineall
    class SimpleDataContainer;
        int value;
        function new(int init_val);
            value = init_val;
        endfunction
    endclass
    SimpleDataContainer my_data_obj;
    always_comb begin
        my_data_obj = new(out_result_a);
        if (my_data_obj.value > 0) begin end
    end
endmodule
module SvPreproc_ParamDefines (
    input logic [15:0] in_x,
    input logic [15:0] in_y,
    output logic [15:0] out_calc_res
);
    `define ADD(a, b) (a + b)
    `define SUBTRACT(x, y=0) (x - y)
    `define NESTED_OP(val_a, val_b) `ADD(val_a, `SUBTRACT(val_b))
    `define MULTIPLY(op1, op2=1) (op1 * op2)
    logic [15:0] temp_sum;
    logic [15:0] temp_diff_default;
    logic [15:0] temp_diff_provided;
    logic [15:0] temp_nested;
    logic [15:0] temp_mult_default;
    logic [15:0] temp_mult_provided;
    assign temp_sum = `ADD(in_x, in_y);
    assign temp_diff_default = `SUBTRACT(in_x);
    assign temp_diff_provided = `SUBTRACT(in_x, in_y);
    assign temp_nested = `NESTED_OP(in_x, in_y);
    assign temp_mult_default = `MULTIPLY(in_x);
    assign temp_mult_provided = `MULTIPLY(in_x, in_y);
    `define PROCESS_ARGS(arg1, arg2) `ADD(`SUBTRACT(arg1, arg2), `MULTIPLY(arg1, arg2))
    logic [15:0] complex_res;
    assign complex_res = `PROCESS_ARGS(in_x, in_y);
    assign out_calc_res = temp_sum + temp_diff_default + temp_diff_provided + temp_nested + temp_mult_default + temp_mult_provided + complex_res;
endmodule
module SvPreproc_Conditionals (
    input logic enable_flag_1,
    input logic enable_flag_2,
    output logic [4:0] out_status_flags
);
    `define FEATURE_ALPHA_DEFINED
    `define ZERO_VAL_MACRO_DEFINED
    `ifndef NON_EXISTENT_FEATURE
        `define CONFIG_STATUS_M 3'd1
    `else
        `define CONFIG_STATUS_M 3'd0
    `endif
    `ifdef FEATURE_ALPHA_DEFINED
        `define PATH_ID_M 3'd2
    `elsif ANOTHER_NON_EXISTENT_FEATURE
        `define PATH_ID_M 3'd3
    `else
        `define PATH_ID_M 3'd4
    `endif
    `ifdef FEATURE_ALPHA_DEFINED
        `ifdef YET_ANOTHER_NON_EXISTENT_FEATURE
            `define NESTED_PATH_M 3'd5
        `else
            `define NESTED_PATH_M 3'd6
        `endif
    `else
        `define NESTED_PATH_M 3'd7
    `endif
    `define COND_FLAG_1
    `ifdef COND_FLAG_1
        `define OUT_COND_1 1'b1
    `else
        `define OUT_COND_1 1'b0
    `endif
    `ifndef COND_FLAG_2
        `define OUT_COND_2 1'b1
    `else
        `define OUT_COND_2 1'b0
    `endif
    `ifdef COND_FLAG_3
        `define OUT_COND_3 1'b1
    `elsif COND_FLAG_4
        `define OUT_COND_3 1'b0
    `else
        `define OUT_COND_3 1'b0
    `endif
    `ifdef ALWAYS_FALSE_MACRO 
        `define EXPR_RESULT 1'b1
    `elsif ALWAYS_TRUE_MACRO_FAKE 
        `define EXPR_RESULT 1'b0
    `elsif FEATURE_ALPHA_DEFINED 
        `define EXPR_RESULT 1'b1
    `else
        `define EXPR_RESULT 1'b0
    `endif
    assign out_status_flags = {`CONFIG_STATUS_M, `PATH_ID_M, `NESTED_PATH_M, `OUT_COND_1, `OUT_COND_2, `EXPR_RESULT};
endmodule
module SvPreproc_StringConcat (
    input logic [7:0] operand_val_in,
    output string out_processed_str
);
    `define STRINGIFY_VAL(X) `"X"`
    `define IDENT_PART_X my_prefix_
    `define IDENT_PART_Y _middle_
    `define IDENT_PART_Z _suffix
    `define CONCAT_THREE_IDS(A, B, C) A``B``C
    `define ESCAPED_Q_STR "This string has an escaped quote: \""`
    `define ESCAPED_BS_STR "This string has a backslash: \\\\ and a newline character: \\n."`
    string s_strify_result;
    string s_concat_result_1;
    string s_concat_result_2;
    string s_escaped_quotes;
    string s_escaped_backslash;
    logic [7:0] my_local_var_for_stringify;
    assign my_local_var_for_stringify = operand_val_in;
    assign s_strify_result = `STRINGIFY_VAL(my_local_var_for_stringify);
    logic [7:0] `CONCAT_THREE_IDS(IDENT_PART_X, IDENT_PART_Y, IDENT_PART_Z);
    assign `CONCAT_THREE_IDS(IDENT_PART_X, IDENT_PART_Y, IDENT_PART_Z) = 8'hC0;
    assign s_concat_result_1 = $sformatf("%s", `CONCAT_THREE_IDS(IDENT_PART_X, IDENT_PART_Y, IDENT_PART_Z));
    logic [7:0] my_prefix_d_p__suffix;
    `define DYNAMIC_PART_FOR_CONCAT_VAL d_p_
    assign my_prefix_d_p__suffix = operand_val_in + 8'h1; 
    assign s_concat_result_2 = $sformatf("%s%0d", my_prefix_d_p__suffix, operand_val_in);
    assign s_escaped_quotes = `ESCAPED_Q_STR;
    assign s_escaped_backslash = `ESCAPED_BS_STR;
    assign out_processed_str = {
        s_strify_result, "_",
        s_concat_result_1, "_",
        s_concat_result_2, "_",
        s_escaped_quotes, "_",
        s_escaped_backslash, "_",
        $sformatf("%h", `CONCAT_THREE_IDS(IDENT_PART_X, IDENT_PART_Y, IDENT_PART_Z))
    };
endmodule
module SvPreproc_IncludesCommentsLine (
    input logic [3:0] in_value,
    output logic [3:0] out_final_value
);
    `define SOME_INTERNAL_VAL 4'd7
    `line 1000 "preproc_test_file.sv" 0
    logic [3:0] temp_val;
    assign temp_val = in_value + `SOME_INTERNAL_VAL;
    `line 2000 "preproc_test_file.sv" 0
    assign out_final_value = temp_val;
endmodule
module SvPreproc_RecursiveRedefines (
    input logic [7:0] input_val_in,
    output logic [7:0] output_val_out
);
    `define MACRO_A `MACRO_B
    `define MACRO_B `MACRO_A
    `define SELF_RECURSIVE `SELF_RECURSIVE_VAL
    `define SELF_RECURSIVE_VAL `SELF_RECURSIVE
    `define SIMPLE_ADD_VAL 8'd5
    assign output_val_out = input_val_in + `SIMPLE_ADD_VAL;
    logic [7:0] dummy_val;
endmodule
