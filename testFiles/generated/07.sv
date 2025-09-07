interface seq2_if;
    logic [7:0] status_byte;
    modport PortB (output status_byte);
endinterface
interface seq_if;
    logic [31:0] value_a;
    modport PortA (output value_a);
endinterface
interface simple_if (
    input logic clk
);
    logic data;
    logic ready;
    modport master (output data, input ready);
    modport slave (input data, output ready);
endinterface
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

module ansi_implicit_inherit (
    input logic [2:0] in1,
    input logic in2,
    output logic extra_out,
    output logic out1,
    output logic out2
);
    always_comb begin
        out1 = |in1;
        out2 = |in2;
        extra_out = out1 ^ out2;
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

module case_priority_overlapping_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        priority casez (case_expr)
            2'b1?: internal_out = 5;
            2'b?1: internal_out = 6;  
            2'b0?: internal_out = 7;
            2'b?0: internal_out = 8;  
            default: internal_out = 9;
        endcase
    end
endmodule

module mod_logical_not (
    input logic cond_in,
    output logic cond_out
);
    always_comb begin
        cond_out = !cond_in;
    end
endmodule

module multiplexer_2to1 (
    input logic data0,
    input logic data1,
    input logic sel,
    output logic result
);
    assign result = sel ? data1 : data0;
endmodule

module nested_module (
    input logic nm_in,
    output logic nm_out
);
    assign nm_out = nm_in;
endmodule

module split_arith_blocking (
    input logic [7:0] op1_u,
    input logic [7:0] op2_u,
    output logic [7:0] diff_u,
    output logic [7:0] prod_u,
    output logic [7:0] sum_u
);
    always @(*) begin
        sum_u = op1_u + op2_u;
        diff_u = op1_u - op2_u;
        prod_u = op1_u * op2_u;
    end
endmodule

module sub_module (
    input logic sub_in,
    output logic sub_out
);
    assign sub_out = !sub_in;
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755004205131_264,
    input logic inj_data1_1755004205165_564,
    input wire [3:0] inj_dffcl_ctrl_mode_1755004205173_237,
    input wire [15:0] inj_dffcl_data_in1_1755004205173_502,
    input wire [15:0] inj_dffcl_data_in2_1755004205173_642,
    input logic inj_enable_1755004205120_840,
    input logic [2:0] inj_in1_1755004205150_515,
    input logic [7:0] inj_in2_1755004205202_53,
    input logic [7:0] inj_in3_1755004205202_188,
    input wire [7:0] inj_in_a_1755004205121_201,
    input wire [7:0] inj_in_b_1755004205121_589,
    input wire [7:0] inj_in_c_1755004205121_944,
    input wire inj_in_cond_neq_lhs_1755004205121_424,
    input wire inj_in_cond_neq_rhs_1755004205121_187,
    input wire inj_in_cond_not_1755004205121_126,
    input wire [7:0] inj_in_not_else_1755004205121_901,
    input wire [7:0] inj_in_not_then_1755004205121_983,
    input int inj_in_val_1755004205138_300,
    input logic [31:0] inj_input1_1755004205119_401,
    input logic [7:0] inj_input2_byte_1755004205119_571,
    input logic inj_sel_1755004205165_116,
    input logic [3:0] inj_val_a_1755004205120_743,
    input logic [3:0] inj_val_b_1755004205120_484,
    input logic [63:0] inj_wide_a_1755004205217_805,
    input logic [63:0] inj_wide_b_1755004205218_290,
    input logic [63:0] inj_wide_c_1755004205218_988,
    input wire reset,
    output logic inj_cond_out_1755004205195_31,
    output logic [7:0] inj_data_out_1755004205153_692,
    output logic [7:0] inj_data_out_k_1755004205225_964,
    output logic [15:0] inj_dffcl_data_out_1755004205173_814,
    output logic [7:0] inj_diff_u_1755004205209_714,
    output logic inj_extra_out_1755004205150_473,
    output logic [4:0] inj_internal_out_1755004205131_487,
    output logic [4:0] inj_internal_out_1755004205147_727,
    output logic [4:0] inj_internal_out_1755004205157_549,
    output logic [4:0] inj_internal_out_1755004205189_184,
    output logic inj_is_even_1755004205120_675,
    output wire inj_loop_out_1755004205135_491,
    output logic inj_main_out_1755004205133_703,
    output logic inj_nand_out_1755004205202_500,
    output logic inj_nm_out_1755004205161_319,
    output logic inj_nor_out_1755004205202_585,
    output logic [7:0] inj_o_array_var_elem_1755004205129_915,
    output logic inj_o_p_and_1755004205182_592,
    output logic inj_o_p_xor_1755004205182_460,
    output logic inj_o_sel_var_bit_1755004205129_761,
    output logic inj_out1_1755004205150_896,
    output logic inj_out2_1755004205150_172,
    output logic [7:0] inj_out_1755004205141_283,
    output logic inj_out_eq_1755004205121_642,
    output logic inj_out_eq_concat_1755004205121_915,
    output logic inj_out_gt_1755004205121_977,
    output logic inj_out_gte_1755004205121_955,
    output logic inj_out_lt_1755004205121_974,
    output logic inj_out_lte_1755004205121_387,
    output logic inj_out_neq_1755004205121_489,
    output logic inj_out_not_eq_1755004205121_712,
    output logic inj_out_not_neq_1755004205121_466,
    output reg inj_out_res_1755004205169_820,
    output logic inj_out_ternary_1755004205121_562,
    output logic inj_out_ternary_1bit_0else_1755004205121_732,
    output logic inj_out_ternary_1bit_0then_1755004205121_884,
    output logic inj_out_ternary_1bit_1else_1755004205121_310,
    output logic inj_out_ternary_1bit_1then_1755004205121_142,
    output logic inj_out_ternary_const_cond_false_1755004205121_380,
    output logic inj_out_ternary_const_cond_true_1755004205121_469,
    output logic [7:0] inj_out_ternary_dec_1755004205121_659,
    output logic [7:0] inj_out_ternary_inc_1755004205121_458,
    output logic [7:0] inj_out_ternary_pulled_nots_1755004205121_245,
    output logic inj_out_ternary_swapped_cond_1755004205121_40,
    output logic inj_out_ternary_swapped_neq_cond_1755004205121_81,
    output int inj_out_val_1755004205137_553,
    output logic [7:0] inj_out_val_1755004205144_693,
    output logic [7:0] inj_prod_u_1755004205209_406,
    output logic [3:0] inj_result_1755004205120_836,
    output logic inj_result_1755004205165_126,
    output logic inj_sequence_valid_1755004205119_566,
    output logic [7:0] inj_sum_u_1755004205209_166,
    output logic [63:0] inj_wide_out_1755004205218_537,
    output logic inj_xnor_out_1755004205202_762
);
    // BEGIN: module_sequence_different_if_ts1755004205120
    // BEGIN: CombinationalLogic_ts1755004205120
    // BEGIN: FunctionTaskMod_ts1755004205120
    function automatic bit check_even(input logic [7:0] v);
        check_even = ~v[0];
    endfunction
    task automatic dummy_task(input logic [7:0] v);
        int tmp_ts1755004205120;
        tmp_ts1755004205120 = v;
    // BEGIN: Mod_TernaryLogic_ts1755004205127
    parameter [7:0] CONST_ONE_8 = 8'h01;
    parameter [0:0] CONST_ZERO_1 = 1'b0;
    parameter [0:0] CONST_ONE_1 = 1'b1;
    logic [7:0] intermediate_const_concat_comp_ts1755004205126;
    logic [15:0] intermediate_concat_comp_src_ts1755004205126;
    // BEGIN: HandleOutOfBoundsRead_ts1755004205129
    parameter ARR_SIZE = 4;
    logic [7:0] my_array_ts1755004205129 [0:ARR_SIZE-1];
    // BEGIN: ModuleGenerateIf_ts1755004205144
    parameter int PROCESS_ENABLE = 1;
    logic [7:0] processed_val_ts1755004205144;
    // BEGIN: SequentialLogic_ts1755004205154
    logic [7:0] internal_reg_ts1755004205154;
    // BEGIN: split_input_only_var_ts1755004205225
    always @(posedge clk) begin
        if (inj_data1_1755004205165_564) begin
            inj_data_out_k_1755004205225_964 <= inj_in2_1755004205202_53;
        end
    end
    // END: split_input_only_var_ts1755004205225

    // BEGIN: wide_ops_deep_ts1755004205218
    assign inj_wide_out_1755004205218_537 = (((inj_wide_a_1755004205217_805 + inj_wide_b_1755004205218_290) ^ inj_wide_c_1755004205218_988) & (~inj_wide_a_1755004205217_805 | inj_wide_b_1755004205218_290)) + (inj_wide_c_1755004205218_988 >>> 5);
    // END: wide_ops_deep_ts1755004205218

    split_arith_blocking split_arith_blocking_inst_1755004205209_9120 (
        .op2_u(inj_in2_1755004205202_53),
        .diff_u(inj_diff_u_1755004205209_714),
        .prod_u(inj_prod_u_1755004205209_406),
        .sum_u(inj_sum_u_1755004205209_166),
        .op1_u(inj_in3_1755004205202_188)
    );
    // BEGIN: remaining_reduction_ops_ts1755004205202
    assign inj_nand_out_1755004205202_500 = ~&inj_input2_byte_1755004205119_571;
    assign inj_nor_out_1755004205202_585 = ~|inj_in2_1755004205202_53;
    assign inj_xnor_out_1755004205202_762 = ^~inj_in3_1755004205202_188;
    // END: remaining_reduction_ops_ts1755004205202

    mod_logical_not mod_logical_not_inst_1755004205195_2957 (
        .cond_in(inj_sel_1755004205165_116),
        .cond_out(inj_cond_out_1755004205195_31)
    );
    // BEGIN: case_full_parallel_mod_ts1755004205189
    always @* begin
        (* full, parallel *)
        case (inj_case_expr_1755004205131_264)
            2'b00: inj_internal_out_1755004205189_184 = 1;
            2'b01: inj_internal_out_1755004205189_184 = 2;
            2'b10: inj_internal_out_1755004205189_184 = 3;
            default: inj_internal_out_1755004205189_184 = 4;
        endcase
    end
    // END: case_full_parallel_mod_ts1755004205189

    // BEGIN: primitive_example_ts1755004205182
    and (inj_o_p_and_1755004205182_592, inj_enable_1755004205120_840, inj_sel_1755004205165_116);
    xor (inj_o_p_xor_1755004205182_460, inj_enable_1755004205120_840, inj_sel_1755004205165_116);
    // END: primitive_example_ts1755004205182

    // BEGIN: deep_ff_control_logic_ts1755004205175
    always_ff @(posedge clk or negedge reset) begin
    if (!reset) begin
        inj_dffcl_data_out_1755004205173_814 <= 16'h0000;
    end else begin
        case (inj_dffcl_ctrl_mode_1755004205173_237)
            4'd0: inj_dffcl_data_out_1755004205173_814 <= inj_dffcl_data_in1_1755004205173_502 + inj_dffcl_data_in2_1755004205173_642;
            4'd1: begin
                if (inj_dffcl_data_in1_1755004205173_502 > inj_dffcl_data_in2_1755004205173_642) begin
                    case (inj_dffcl_ctrl_mode_1755004205173_237[1:0])
                        2'b00: inj_dffcl_data_out_1755004205173_814 <= inj_dffcl_data_in1_1755004205173_502 - inj_dffcl_data_in2_1755004205173_642;
                        2'b01: inj_dffcl_data_out_1755004205173_814 <= inj_dffcl_data_in1_1755004205173_502 & inj_dffcl_data_in2_1755004205173_642;
                        default: inj_dffcl_data_out_1755004205173_814 <= inj_dffcl_data_in1_1755004205173_502 | inj_dffcl_data_in2_1755004205173_642;
                    endcase
                end else begin
                    case (inj_dffcl_ctrl_mode_1755004205173_237[1:0])
                        2'b00: inj_dffcl_data_out_1755004205173_814 <= inj_dffcl_data_in2_1755004205173_642 - inj_dffcl_data_in1_1755004205173_502;
                        2'b01: inj_dffcl_data_out_1755004205173_814 <= inj_dffcl_data_in1_1755004205173_502 ^ inj_dffcl_data_in2_1755004205173_642;
                        default: inj_dffcl_data_out_1755004205173_814 <= ~inj_dffcl_data_in1_1755004205173_502;
                    endcase
                end
            end
            4'd2: begin
                casez (inj_dffcl_data_in1_1755004205173_502[15:13])
                    3'b000: inj_dffcl_data_out_1755004205173_814 <= inj_dffcl_data_in2_1755004205173_642;
                    3'b001: inj_dffcl_data_out_1755004205173_814 <= ~inj_dffcl_data_in2_1755004205173_642;
                    3'b01?: begin
                        if (inj_dffcl_data_in2_1755004205173_642[0]) inj_dffcl_data_out_1755004205173_814 <= inj_dffcl_data_in1_1755004205173_502 << 1;
                        else inj_dffcl_data_out_1755004205173_814 <= inj_dffcl_data_in1_1755004205173_502 >> 1;
                    end
                    3'b1??: begin
                        if (inj_dffcl_ctrl_mode_1755004205173_237[0]) inj_dffcl_data_out_1755004205173_814 <= inj_dffcl_data_in1_1755004205173_502 + 1;
                        else inj_dffcl_data_out_1755004205173_814 <= inj_dffcl_data_in1_1755004205173_502 - 1;
                    end
                    default: inj_dffcl_data_out_1755004205173_814 <= 16'hAAAA;
                endcase
            end
            default: begin
                if (inj_dffcl_ctrl_mode_1755004205173_237[2]) inj_dffcl_data_out_1755004205173_814 <= inj_dffcl_data_in1_1755004205173_502;
                else inj_dffcl_data_out_1755004205173_814 <= inj_dffcl_data_in2_1755004205173_642;
            end
        endcase
    end
    end
    // END: deep_ff_control_logic_ts1755004205175

    case_basic case_basic_inst_1755004205169_6113 (
        .in_val(inj_case_expr_1755004205131_264),
        .out_res(inj_out_res_1755004205169_820)
    );
    multiplexer_2to1 multiplexer_2to1_inst_1755004205165_3046 (
        .sel(inj_sel_1755004205165_116),
        .result(inj_result_1755004205165_126),
        .data0(inj_enable_1755004205120_840),
        .data1(inj_data1_1755004205165_564)
    );
    nested_module nested_module_inst_1755004205161_8653 (
        .nm_out(inj_nm_out_1755004205161_319),
        .nm_in(inj_enable_1755004205120_840)
    );
    // BEGIN: case_unique_casez_reordered_mod_ts1755004205157
    always @* begin
        unique casez ({inj_case_expr_1755004205131_264[0], inj_val_b_1755004205120_484[3:2], inj_case_expr_1755004205131_264[1]})
            4'b1?0?: inj_internal_out_1755004205157_549 = 30;
            4'b?101: inj_internal_out_1755004205157_549 = 31;  
            4'b0?1?: inj_internal_out_1755004205157_549 = 32;
            4'b1?1?: inj_internal_out_1755004205157_549 = 33;  
            4'b?111: inj_internal_out_1755004205157_549 = 34;  
        endcase
    end
    // END: case_unique_casez_reordered_mod_ts1755004205157

    always @(posedge clk or negedge reset) begin
        if (~reset) begin
            internal_reg_ts1755004205154 <= 8'h00;
        end else begin
            internal_reg_ts1755004205154 <= inj_input2_byte_1755004205119_571;
        end
    end
    assign inj_data_out_1755004205153_692 = internal_reg_ts1755004205154;
    // END: SequentialLogic_ts1755004205154

    ansi_implicit_inherit ansi_implicit_inherit_inst_1755004205150_8246 (
        .in1(inj_in1_1755004205150_515),
        .in2(inj_enable_1755004205120_840),
        .extra_out(inj_extra_out_1755004205150_473),
        .out1(inj_out1_1755004205150_896),
        .out2(inj_out2_1755004205150_172)
    );
    case_priority_overlapping_mod case_priority_overlapping_mod_inst_1755004205147_7598 (
        .case_expr(inj_case_expr_1755004205131_264),
        .internal_out(inj_internal_out_1755004205147_727)
    );
    generate
        if (PROCESS_ENABLE) begin : process_block
            assign processed_val_ts1755004205144 = inj_input2_byte_1755004205119_571 + 10;
        end else begin : bypass_block
            assign processed_val_ts1755004205144 = inj_input2_byte_1755004205119_571;
        end
    endgenerate
    assign inj_out_val_1755004205144_693 = processed_val_ts1755004205144;
    // END: ModuleGenerateIf_ts1755004205144

    // BEGIN: sub_inst_array_mod_ts1755004205142
    assign inj_out_1755004205141_283 = inj_input2_byte_1755004205119_571;
    // END: sub_inst_array_mod_ts1755004205142

    // BEGIN: definition_used_diag_mod_ts1755004205138
    assign inj_out_val_1755004205137_553 = inj_in_val_1755004205138_300;
    // END: definition_used_diag_mod_ts1755004205138

    Comb_Loop Comb_Loop_inst_1755004205135_7121 (
        .loop_in(inj_in_cond_neq_lhs_1755004205121_424),
        .loop_out(inj_loop_out_1755004205135_491)
    );
    // BEGIN: hierarchy_if_ts1755004205133
    sub_module u_sub (
        .sub_in(inj_enable_1755004205120_840),
        .sub_out(inj_main_out_1755004205133_703)
    );
    simple_if if_inst (.clk(clk));
    always_comb begin
        if_inst.data = inj_enable_1755004205120_840;
        if_inst.ready = inj_main_out_1755004205133_703;
    end
    // END: hierarchy_if_ts1755004205133

    case_priority_overlapping_mod case_priority_overlapping_mod_inst_1755004205131_6715 (
        .case_expr(inj_case_expr_1755004205131_264),
        .internal_out(inj_internal_out_1755004205131_487)
    );
    assign my_array_ts1755004205129[0] = 8'd10;
    assign my_array_ts1755004205129[1] = 8'd20;
    assign my_array_ts1755004205129[2] = 8'd30;
    assign my_array_ts1755004205129[3] = 8'd40;
    assign inj_o_sel_var_bit_1755004205129_761 = inj_input2_byte_1755004205119_571[inj_val_b_1755004205120_484];
    assign inj_o_array_var_elem_1755004205129_915 = my_array_ts1755004205129[inj_val_a_1755004205120_743];
    // END: HandleOutOfBoundsRead_ts1755004205129

    always_comb begin
        inj_out_eq_1755004205121_642 = (inj_in_a_1755004205121_201 == inj_in_b_1755004205121_589);
        inj_out_neq_1755004205121_489 = (inj_in_a_1755004205121_201 != inj_in_b_1755004205121_589);
        inj_out_gt_1755004205121_977 = (inj_in_a_1755004205121_201 > inj_in_b_1755004205121_589);
        inj_out_lt_1755004205121_974 = (inj_in_a_1755004205121_201 < inj_in_b_1755004205121_589);
        inj_out_gte_1755004205121_955 = (inj_in_a_1755004205121_201 >= inj_in_b_1755004205121_589);
        inj_out_lte_1755004205121_387 = (inj_in_a_1755004205121_201 <= inj_in_b_1755004205121_589);
        inj_out_not_eq_1755004205121_712 = !(inj_in_a_1755004205121_201 == inj_in_b_1755004205121_589);
        inj_out_not_neq_1755004205121_466 = !(inj_in_a_1755004205121_201 != inj_in_b_1755004205121_589);
        intermediate_const_concat_comp_ts1755004205126 = 8'hAA;
        intermediate_concat_comp_src_ts1755004205126 = {inj_in_a_1755004205121_201, inj_in_b_1755004205121_589};
        inj_out_eq_concat_1755004205121_915 = (intermediate_const_concat_comp_ts1755004205126 == intermediate_concat_comp_src_ts1755004205126[7:0]);
        inj_out_ternary_1755004205121_562 = reset ? inj_in_a_1755004205121_201[0] : inj_in_b_1755004205121_589[0];
        inj_out_ternary_const_cond_true_1755004205121_469 = 1'b1 ? inj_in_a_1755004205121_201[0] : inj_in_b_1755004205121_589[0];
        inj_out_ternary_const_cond_false_1755004205121_380 = 1'b0 ? inj_in_a_1755004205121_201[0] : inj_in_b_1755004205121_589[0];
        inj_out_ternary_swapped_cond_1755004205121_40 = !inj_in_cond_not_1755004205121_126 ? inj_in_a_1755004205121_201[0] : inj_in_b_1755004205121_589[0];
        inj_out_ternary_swapped_neq_cond_1755004205121_81 = (inj_in_cond_neq_lhs_1755004205121_424 != inj_in_cond_neq_rhs_1755004205121_187) ? inj_in_a_1755004205121_201[0] : inj_in_b_1755004205121_589[0];
        inj_out_ternary_pulled_nots_1755004205121_245 = reset ? ~inj_in_not_then_1755004205121_983 : ~inj_in_not_else_1755004205121_901;
        inj_out_ternary_inc_1755004205121_458 = reset ? (inj_in_a_1755004205121_201 + CONST_ONE_8) : inj_in_a_1755004205121_201;
        inj_out_ternary_dec_1755004205121_659 = reset ? (inj_in_a_1755004205121_201 - CONST_ONE_8) : inj_in_a_1755004205121_201;
        inj_out_ternary_1bit_0then_1755004205121_884 = reset ? CONST_ZERO_1 : clk;
        inj_out_ternary_1bit_1then_1755004205121_142 = reset ? CONST_ONE_1 : clk;
        inj_out_ternary_1bit_0else_1755004205121_732 = reset ? clk : CONST_ZERO_1;
        inj_out_ternary_1bit_1else_1755004205121_310 = reset ? clk : CONST_ONE_1;
    end
    // END: Mod_TernaryLogic_ts1755004205127

    endtask
    assign inj_is_even_1755004205120_675 = check_even(inj_input2_byte_1755004205119_571);
    // END: FunctionTaskMod_ts1755004205120

    always_comb begin
        if (inj_enable_1755004205120_840) begin
            inj_result_1755004205120_836 = inj_val_a_1755004205120_743 + inj_val_b_1755004205120_484;
        end else begin
            inj_result_1755004205120_836 = 4'h0;
        end
    end
    // END: CombinationalLogic_ts1755004205120

    seq_if sif_port();
    seq2_if sif2_port();
    always_comb begin
        sif_port.value_a = inj_input1_1755004205119_401;
        sif2_port.status_byte = inj_input2_byte_1755004205119_571;
        inj_sequence_valid_1755004205119_566 = 1'b1;
    end
    // END: module_sequence_different_if_ts1755004205120
endmodule

