module PragmaOnceDirective (
    input bit trigger_input,
    output bit trigger_output
);
assign trigger_output = trigger_input;
endmodule

module attributes_test (
    input logic i_attr_in,
    output logic o_attr_out
);
    (* synthesis_preserve *) logic internal_signal;
    always_comb begin : my_combinational_block
        internal_signal = i_attr_in ? 1'b1 : 1'b0;
        o_attr_out      = internal_signal;
    end
endmodule

module case_basic (
    input logic [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b00: out_res = 1'b0;
            2'b01: out_res = 1'b1;
            2'b10: out_res = 1'b0;
            2'b11: out_res = 1'b1;
        endcase
    end
endmodule

module child_module_v2_config_dummy (
    input logic i,
    output logic o
);
    assign o = i | i; 
endmodule

module split_nested_if (
    input logic clk_m,
    input logic cond1_m,
    input logic cond2_m,
    input logic [7:0] val_a_m,
    input logic [7:0] val_b_m,
    input logic [7:0] val_c_m,
    output logic [7:0] result_m
);
    always @(posedge clk_m) begin
        if (cond1_m) begin
            if (cond2_m) begin
                result_m <= val_a_m;
            end else begin
                result_m <= val_b_m;
            end
        end else begin
            result_m <= val_c_m;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_cond2_m_1755007868077_162,
    input logic inj_i_attr_in_1755007868074_975,
    input int inj_i_val_1755007868071_436,
    input logic [7:0] inj_in2_a_1755007868075_380,
    input logic [1:0] inj_in_val_1755007868071_317,
    input logic [3:0] inj_in_vector_1755007868080_995,
    input bit inj_trigger_input_1755007868071_987,
    input logic [7:0] inj_val_b_m_1755007868077_933,
    input logic [7:0] inj_val_c_m_1755007868077_767,
    input wire reset,
    output logic inj_o_1755007868079_425,
    output logic inj_o_attr_out_1755007868074_960,
    output int inj_o_val_1755007868071_189,
    output logic [7:0] inj_out2_a_1755007868075_233,
    output reg inj_out_res_1755007868071_218,
    output logic inj_out_single_1755007868080_520,
    output logic [7:0] inj_result_m_1755007868077_16,
    output logic [3:0] inj_test_case_result_1755007868072_288,
    output bit inj_trigger_output_1755007868071_333
);
    // BEGIN: mod_automatic_task_ts1755007868071
    task automatic update_val(input int in_v, output int out_v);
        out_v = in_v * 2;
    endtask
    always_comb begin
        int temp_val_ts1755007868071;
            // BEGIN: combinatorial_logic_ts1755007868081
            always_comb begin
                if (inj_in_vector_1755007868080_995 > 4'd5) begin
                    inj_out_single_1755007868080_520 = 1'b1;
                end else begin
                    inj_out_single_1755007868080_520 = 1'b0;
                end
            end
            // END: combinatorial_logic_ts1755007868081

            child_module_v2_config_dummy child_module_v2_config_dummy_inst_1755007868079_7638 (
                .o(inj_o_1755007868079_425),
                .i(inj_cond2_m_1755007868077_162)
            );
            split_nested_if split_nested_if_inst_1755007868077_5794 (
                .result_m(inj_result_m_1755007868077_16),
                .clk_m(clk),
                .cond1_m(inj_i_attr_in_1755007868074_975),
                .cond2_m(inj_cond2_m_1755007868077_162),
                .val_a_m(inj_in2_a_1755007868075_380),
                .val_b_m(inj_val_b_m_1755007868077_933),
                .val_c_m(inj_val_c_m_1755007868077_767)
            );
            // BEGIN: split_basic_nonblocking_ts1755007868075
            always @(posedge clk) begin
                inj_out2_a_1755007868075_233 <= inj_in2_a_1755007868075_380;
            end
            // END: split_basic_nonblocking_ts1755007868075

            attributes_test attributes_test_inst_1755007868074_7779 (
                .i_attr_in(inj_i_attr_in_1755007868074_975),
                .o_attr_out(inj_o_attr_out_1755007868074_960)
            );
            // BEGIN: PragmaSyntaxVariety_ts1755007868072
        `ifdef SLANG_PRAGMA
        `unknown_pragma_real 1.23;
        `endif
        `ifdef SLANG_PRAGMA
        `unknown_slang_pragma (arg1, arg2="value")
        `endif
        `ifdef SLANG_PRAGMA
        `protect (1 + 2)
        `endif
        `ifdef SLANG_PRAGMA
        `protect {3, 4}
        `endif
        `ifdef SLANG_PRAGMA
        `protect unknown_action (arg=1)
        `endif
        `ifdef SLANG_PRAGMA
        `protect encoding
        `endif
        `ifdef SLANG_PRAGMA
        `protect encoding (enctype="raw", "string_arg_only")
        `endif
        `ifdef SLANG_PRAGMA
        `protect encoding (enctype="raw", unknown_option=99)
        `endif
        `ifdef SLANG_PRAGMA
        `protect encoding (bytes=-10)
        `endif
        `ifdef SLANG_PRAGMA
        `protect license (match="not_an_integer")
        `endif
        `ifdef SLANG_PRAGMA
        `protect license (match=42.5)
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport (obj="a", acc="b", extra=1)
        `endif
        `ifdef SLANG_PRAGMA
        `protect begin (arg_present)
        `endif
        `ifdef SLANG_PRAGMA
        `protect license ("license_string_only")
        `endif
        `ifdef SLANG_PRAGMA
        `protect license (library=my_library_ident)
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport (obj="a")
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport (obj="a", acc="b", c=3)
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport (obj="a", "access_string")
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport ("object_string", acc="b")
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport (object="a", access=123)
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport (object=123, access="b")
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport (not_object="a", access="b")
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport (object="a", not_access="b")
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic (1 + 2)
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic unknown_action_diag
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic level=warn
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic ignore (value=(1+2))
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic ignore (value=(value=1))
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic ignore (value=some_identifier)
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic warn (value=12345)
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic ignore simple_identifier_arg
        `endif
        `ifdef SLANG_PRAGMA
        `protect "simple_string_argument"
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic ignore "just_a_string_diag_code"
        `endif
        assign inj_test_case_result_1755007868072_288 = (inj_in_val_1755007868071_317 == 2'b01) ? 4'h5 : 4'hA;
            // END: PragmaSyntaxVariety_ts1755007868072

            case_basic case_basic_inst_1755007868071_6481 (
                .out_res(inj_out_res_1755007868071_218),
                .in_val(inj_in_val_1755007868071_317)
            );
        update_val(inj_i_val_1755007868071_436, temp_val_ts1755007868071);
        inj_o_val_1755007868071_189 = temp_val_ts1755007868071;
    end
    // END: mod_automatic_task_ts1755007868071

    PragmaOnceDirective PragmaOnceDirective_inst_1755007868071_11 (
        .trigger_input(inj_trigger_input_1755007868071_987),
        .trigger_output(inj_trigger_output_1755007868071_333)
    );
endmodule

