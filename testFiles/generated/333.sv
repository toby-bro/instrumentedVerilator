module Comb_Loop (
    input wire loop_in,
    output wire loop_out
);
    wire loop_wire1;
    wire loop_wire2;
    assign loop_wire1 = loop_wire2 | loop_in;
    assign loop_wire2 = loop_wire1; 
    assign loop_out = loop_wire1;
endmodule

module GenerateIfParam #(
    parameter bit GEN = 1
) (
    input logic sig_in,
    output logic sig_out
);
    generate
        if (GEN) begin : g_true
            assign sig_out = sig_in;
        end
        else begin : g_false
            assign sig_out = ~sig_in;
        end
    endgenerate
endmodule

module LintUnusedSignal (
    input logic in_a,
    output logic out_b
);
    logic unused_w; 
    assign out_b = in_a;
endmodule

module PragmaOnceDirective (
    input bit trigger_input,
    output bit trigger_output
);
assign trigger_output = trigger_input;
endmodule

module arith_comp_ops (
    input logic [15:0] in1,
    input logic [15:0] in2,
    input logic [15:0] in3,
    input logic [15:0] in4,
    input logic [15:0] in5,
    output logic out
);
    assign out = (in1 + in2) * in3 > in4 - in5;
endmodule

module mod_lint_target (
    input wire i_a,
    input wire i_b,
    output logic o_sum,
    output logic [7:0] wide_reg
);
    logic l_reg;
    always_comb begin
        l_reg = 1;
        wide_reg = {i_a, i_b};
    end
    assign o_sum = i_a + i_b;
endmodule

module mod_simple (
    input wire in,
    output wire out
);
    assign out = in;
endmodule

module packed_struct_module (
    input wire [15:0] in_packed_data,
    output wire [7:0] out_byte
);
    typedef struct packed {
        logic [7:0] byte1;
        logic [7:0] byte2;
    } my_packed_struct_t;
    my_packed_struct_t data_struct;
    assign data_struct = in_packed_data;
    assign out_byte = data_struct.byte1;
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module split_basic_nonblocking (
    input logic clk_b,
    input logic [7:0] in2_a,
    output logic [7:0] out2_a
);
    always @(posedge clk_b) begin
        out2_a <= in2_a;
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_data2_1755007866097_449,
    input logic [7:0] inj_data3_1755007866097_653,
    input logic [15:0] inj_in1_1755007866090_754,
    input logic [15:0] inj_in2_1755007866090_104,
    input logic [7:0] inj_in2_a_1755007866084_834,
    input logic [15:0] inj_in3_1755007866090_148,
    input logic [15:0] inj_in4_1755007866090_457,
    input logic [15:0] inj_in5_1755007866090_652,
    input wire [7:0] inj_in_func_a_1755007866095_916,
    input wire [7:0] inj_in_func_b_1755007866095_358,
    input wire [15:0] inj_in_packed_data_1755007866124_797,
    input int inj_in_val_1755007866147_560,
    input logic [4:0] inj_read_address_1755007866085_176,
    input logic [1:0] inj_sel_code_1755007866097_17,
    input bit inj_trigger_input_1755007866086_113,
    input logic [4:0] inj_write_address_1755007866085_721,
    input logic inj_write_en_1755007866085_535,
    input wire reset,
    output wire inj_data_d_1755007866084_960,
    output wire inj_loop_out_1755007866088_42,
    output logic inj_o_out_1755007866119_739,
    output logic inj_o_p_and_1755007866110_862,
    output logic inj_o_p_xor_1755007866110_560,
    output logic inj_o_sum_1755007866087_485,
    output logic inj_o_sum_1755007866100_816,
    output logic [31:0] inj_out1_1755007866105_606,
    output logic [7:0] inj_out1_z_1755007866086_347,
    output logic [7:0] inj_out2_a_1755007866084_983,
    output logic [7:0] inj_out2_z_1755007866086_321,
    output logic inj_out_1755007866090_281,
    output wire inj_out_1755007866091_757,
    output logic inj_out_b_1755007866094_796,
    output logic inj_out_b_1755007866141_517,
    output logic [1:0] inj_out_bits_1755007866135_888,
    output wire [7:0] inj_out_byte_1755007866124_262,
    output logic [7:0] inj_out_func_result_1755007866095_380,
    output logic [7:0] inj_out_reg_h_1755007866092_709,
    output reg inj_out_res_1755007866129_53,
    output int inj_out_val_1755007866147_309,
    output logic inj_out_valid_1755007866089_472,
    output logic [7:0] inj_out_vec_1755007866084_501,
    output logic [7:0] inj_read_data_1755007866085_407,
    output logic [7:0] inj_selected_data_1755007866097_407,
    output logic inj_sig_out_1755007866107_469,
    output logic inj_sum_1755007866153_832,
    output logic [3:0] inj_test_case_result_1755007866113_519,
    output bit inj_trigger_output_1755007866086_972,
    output logic [7:0] inj_wide_reg_1755007866087_878,
    output logic [7:0] inj_wide_reg_1755007866100_275
);
    // BEGIN: simple_logic_b_ts1755007866084
    // BEGIN: SimpleLoopExample_ts1755007866085
    // BEGIN: SynchronousMemory_ts1755007866085
    logic [7:0] mem_ts1755007866085 [0:31];
        // BEGIN: ModuleImplicitPort_ts1755007866089
        logic valid_ts1755007866089;
            // BEGIN: module_function_ts1755007866095
            function automatic [7:0] add_and_subtract;
            input [7:0] val1;
            input [7:0] val2;
            reg [7:0] temp_ts1755007866095;
                // BEGIN: mod_lint_target_ts1755007866101
                logic l_reg_ts1755007866101;
                    // BEGIN: cast_select_demo_ts1755007866135
                    logic [7:0] internal_ts1755007866135;
                        // BEGIN: LintUnusedSignal_ts1755007866142
                        logic unused_w_ts1755007866142; 
                            simple_adder simple_adder_inst_1755007866153_9283 (
                                .a(l_reg_ts1755007866101),
                                .b(inj_write_en_1755007866085_535),
                                .sum(inj_sum_1755007866153_832)
                            );
                            // BEGIN: simple_undeclared_mod_ts1755007866147
                            assign inj_out_val_1755007866147_309 = inj_in_val_1755007866147_560;
                            // END: simple_undeclared_mod_ts1755007866147

                        assign inj_out_b_1755007866141_517 = valid_ts1755007866089;
                        // END: LintUnusedSignal_ts1755007866142

                    always_comb begin
                        internal_ts1755007866135 = inj_data2_1755007866097_449;
                        inj_out_bits_1755007866135_888 = internal_ts1755007866135[3 -: 2];
                    end
                    // END: cast_select_demo_ts1755007866135

                    // BEGIN: case_basic_ts1755007866129
                    always_comb begin
                        inj_out_res_1755007866129_53 = 1'b0;
                        case (inj_sel_code_1755007866097_17)
                            2'b00: inj_out_res_1755007866129_53 = 1'b0;
                            2'b01: inj_out_res_1755007866129_53 = 1'b1;
                            2'b10: inj_out_res_1755007866129_53 = 1'b0;
                            2'b11: inj_out_res_1755007866129_53 = 1'b1;
                        endcase
                    end
                    // END: case_basic_ts1755007866129

                    packed_struct_module packed_struct_module_inst_1755007866124_639 (
                        .out_byte(inj_out_byte_1755007866124_262),
                        .in_packed_data(inj_in_packed_data_1755007866124_797)
                    );
                    // BEGIN: extern_declarations_ts1755007866119
                    assign inj_o_out_1755007866119_739 = l_reg_ts1755007866101;
                    // END: extern_declarations_ts1755007866119

                    // BEGIN: PragmaSyntaxVariety_ts1755007866114
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
                assign inj_test_case_result_1755007866113_519 = (inj_sel_code_1755007866097_17 == 2'b01) ? 4'h5 : 4'hA;
                    // END: PragmaSyntaxVariety_ts1755007866114

                    // BEGIN: primitive_example_ts1755007866110
                    and (inj_o_p_and_1755007866110_862, inj_write_en_1755007866085_535, valid_ts1755007866089);
                    xor (inj_o_p_xor_1755007866110_560, inj_write_en_1755007866085_535, valid_ts1755007866089);
                    // END: primitive_example_ts1755007866110

                    GenerateIfParam GenerateIfParam_inst_1755007866107_1254 (
                        .sig_out(inj_sig_out_1755007866107_469),
                        .sig_in(valid_ts1755007866089)
                    );
                    // BEGIN: simple_macro_user_ts1755007866105
                    `define SIMPLE_VALUE 32'd12345
                    `define ANOTHER_SIMPLE (1 + 2)
                    assign inj_out1_1755007866105_606 = valid_ts1755007866089 ? (`SIMPLE_VALUE + `ANOTHER_SIMPLE) : 32'd0;
                    // END: simple_macro_user_ts1755007866105

                always_comb begin
                    l_reg_ts1755007866101 = 1;
                    inj_wide_reg_1755007866100_275 = {reset, clk};
                end
                assign inj_o_sum_1755007866100_816 = reset + clk;
                // END: mod_lint_target_ts1755007866101

                // BEGIN: IfElseIfChain_ts1755007866098
                always_comb begin
                    if (inj_sel_code_1755007866097_17 == 2'b00) begin
                        inj_selected_data_1755007866097_407 = inj_in2_a_1755007866084_834;
                    end else if (inj_sel_code_1755007866097_17 == 2'b01) begin
                        inj_selected_data_1755007866097_407 = mem_ts1755007866085;
                    end else if (inj_sel_code_1755007866097_17 == 2'b10) begin
                        inj_selected_data_1755007866097_407 = inj_data2_1755007866097_449;
                    end else begin
                        inj_selected_data_1755007866097_407 = inj_data3_1755007866097_653;
                    end
                end
                // END: IfElseIfChain_ts1755007866098

            begin
            temp_ts1755007866095 = val1 + val2;
            add_and_subtract = temp_ts1755007866095 - 1;
            end
            endfunction
            always_comb begin
            inj_out_func_result_1755007866095_380 = add_and_subtract(inj_in_func_a_1755007866095_916, inj_in_func_b_1755007866095_358);
            end
            // END: module_function_ts1755007866095

            LintUnusedSignal LintUnusedSignal_inst_1755007866094_5251 (
                .out_b(inj_out_b_1755007866094_796),
                .in_a(valid_ts1755007866089)
            );
            // BEGIN: split_if_only_then_ts1755007866092
            always @(posedge clk) begin
                if (inj_write_en_1755007866085_535) begin
                    inj_out_reg_h_1755007866092_709 <= mem_ts1755007866085;
                end
            end
            // END: split_if_only_then_ts1755007866092

            mod_simple mod_simple_inst_1755007866091_2822 (
                .out(inj_out_1755007866091_757),
                .in(reset)
            );
            arith_comp_ops arith_comp_ops_inst_1755007866090_8228 (
                .in1(inj_in1_1755007866090_754),
                .in2(inj_in2_1755007866090_104),
                .in3(inj_in3_1755007866090_148),
                .in4(inj_in4_1755007866090_457),
                .in5(inj_in5_1755007866090_652),
                .out(inj_out_1755007866090_281)
            );
        assign valid_ts1755007866089 = |inj_in2_a_1755007866084_834;
        assign inj_out_valid_1755007866089_472 = valid_ts1755007866089;
        // END: ModuleImplicitPort_ts1755007866089

        Comb_Loop Comb_Loop_inst_1755007866088_375 (
            .loop_in(clk),
            .loop_out(inj_loop_out_1755007866088_42)
        );
        mod_lint_target mod_lint_target_inst_1755007866087_3872 (
            .o_sum(inj_o_sum_1755007866087_485),
            .wide_reg(inj_wide_reg_1755007866087_878),
            .i_a(clk),
            .i_b(reset)
        );
        PragmaOnceDirective PragmaOnceDirective_inst_1755007866086_6556 (
            .trigger_input(inj_trigger_input_1755007866086_113),
            .trigger_output(inj_trigger_output_1755007866086_972)
        );
        // BEGIN: split_diff_vars_branches_ts1755007866086
        always @(posedge clk) begin
            if (inj_write_en_1755007866085_535) begin
                inj_out1_z_1755007866086_347 <= mem_ts1755007866085;
            end else begin
                inj_out2_z_1755007866086_321 <= inj_in2_a_1755007866084_834;
            end
        end
        // END: split_diff_vars_branches_ts1755007866086

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            inj_read_data_1755007866085_407 <= 8'h0;
        end else begin
            if (inj_write_en_1755007866085_535) begin
                mem_ts1755007866085[inj_write_address_1755007866085_721] <= inj_in2_a_1755007866084_834;
            end
            inj_read_data_1755007866085_407 <= mem_ts1755007866085[inj_read_address_1755007866085_176];
        end
    end
    // END: SynchronousMemory_ts1755007866085

    always_comb begin
        for (int i = 0; i < 8; i++) begin
            inj_out_vec_1755007866084_501[i] = inj_in2_a_1755007866084_834[7 - i];
        end
    end
    // END: SimpleLoopExample_ts1755007866085

    split_basic_nonblocking split_basic_nonblocking_inst_1755007866084_2127 (
        .clk_b(clk),
        .in2_a(inj_in2_a_1755007866084_834),
        .out2_a(inj_out2_a_1755007866084_983)
    );
    assign inj_data_d_1755007866084_960 = clk;
    // END: simple_logic_b_ts1755007866084
endmodule

