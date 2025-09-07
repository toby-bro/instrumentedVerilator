interface cond_if;
    logic [15:0] control_reg;
    logic [15:0] status_reg;
    modport CtrlStat (output control_reg, input status_reg);
endinterface
module CaseZExample (
    input wire [3:0] data_in,
    input wire [1:0] sel,
    output reg [3:0] case_out
);
    wire [3:0] local_data;
    assign local_data = data_in;
    always @* begin
        casez (sel)
            2'b0?: case_out = local_data;
            2'b10: case_out = 4'b1111;
            default: case_out = 4'b0000;
        endcase
    end
endmodule

module ModWideBus (
    input logic [31:0] data_in_w,
    output logic [31:0] data_out_w
);
    assign data_out_w = ~data_in_w;
endmodule

module mod_basic_bind (
    input logic in1_bind_def,
    output logic out1_bind_def
);
    assign out1_bind_def = ~in1_bind_def;
endmodule

module module_selection (
    input wire in_bit,
    input wire [2:0] in_index,
    input wire [1:0] in_part_lsb,
    input wire [7:0] in_vector,
    output logic out_bit_select,
    output logic [7:0] out_bitwise_ops,
    output logic [3:0] out_part_select,
    output logic [7:0] out_vector_assign
);
    always_comb begin
    out_vector_assign = in_vector;
    out_bit_select = in_vector[in_index];
    out_part_select = in_vector[in_part_lsb +: 4];
    out_bitwise_ops = in_vector & {8{in_bit}};
    end
endmodule

module split_case (
    input logic clk_w,
    input logic [7:0] d0_w,
    input logic [7:0] d1_w,
    input logic [7:0] d2_w,
    input logic [7:0] d3_w,
    input logic [1:0] sel_w,
    output logic [7:0] out_w
);
    always @(posedge clk_w) begin
        case (sel_w)
            2'b00: out_w <= d0_w;
            2'b01: out_w <= d1_w;
            2'b10: out_w <= d2_w;
            default: out_w <= d3_w;
        endcase
    end
endmodule

module snippet (
    input wire clk,
    input logic [15:0] inj_data_in_1755007764788_778,
    input wire [3:0] inj_data_in_1755007764790_520,
    input logic [31:0] inj_data_in_w_1755007764795_292,
    input logic inj_in1_1755007764779_320,
    input logic inj_in2_1755007764779_45,
    input wire [7:0] inj_in_a_1755007764780_434,
    input wire [7:0] inj_in_b_1755007764780_604,
    input wire [7:0] inj_in_c_1755007764780_868,
    input wire [7:0] inj_in_const1_1755007764780_772,
    input wire [7:0] inj_in_const2_1755007764780_567,
    input wire [2:0] inj_in_index_1755007764791_951,
    input logic [7:0] inj_in_q_1755007764779_773,
    input wire [1:0] inj_sel_1755007764790_615,
    input logic [1:0] inj_sel_w_1755007764799_734,
    input wire reset,
    output logic inj_and_reduce_1755007764805_65,
    output logic inj_anded_1755007764802_703,
    output reg [3:0] inj_case_out_1755007764790_549,
    output logic inj_control_status_1755007764788_543,
    output logic inj_control_status_1755007764814_204,
    output logic [31:0] inj_data_out_w_1755007764795_797,
    output logic inj_diff_1755007764802_27,
    output wire inj_dout_1755007764808_751,
    output logic inj_keyword_out_1755007764793_199,
    output logic [3:0] inj_o_out_1755007764797_76,
    output logic inj_or_reduce_1755007764805_569,
    output logic inj_ored_1755007764802_54,
    output logic inj_out1_bind_def_1755007764787_749,
    output logic inj_out_1755007764779_560,
    output logic inj_out_1755007764811_832,
    output logic [7:0] inj_out_add_assoc_1755007764780_935,
    output logic [7:0] inj_out_and_assoc_1755007764780_785,
    output logic [7:0] inj_out_and_swap_const_1755007764780_749,
    output logic [7:0] inj_out_arith_1755007764780_94,
    output logic inj_out_bit_select_1755007764791_137,
    output logic [7:0] inj_out_bitwise_1755007764780_128,
    output logic [7:0] inj_out_bitwise_ops_1755007764791_39,
    output logic inj_out_logical_1755007764780_436,
    output logic [7:0] inj_out_mul_assoc_1755007764780_51,
    output logic [7:0] inj_out_negate_1755007764780_915,
    output logic [7:0] inj_out_or_assoc_1755007764780_236,
    output logic [7:0] inj_out_or_swap_not_1755007764780_45,
    output logic [3:0] inj_out_part_select_1755007764791_653,
    output logic [7:0] inj_out_q_1755007764779_742,
    output logic [7:0] inj_out_unary_not_1755007764780_824,
    output logic [7:0] inj_out_vector_assign_1755007764791_423,
    output logic [7:0] inj_out_w_1755007764799_288,
    output logic [7:0] inj_out_xor_assoc_1755007764780_155,
    output logic [7:0] inj_out_xor_swap_var_1755007764780_877,
    output logic [7:0] inj_sum_1755007764802_110,
    output logic inj_xor_reduce_1755007764805_569,
    output logic inj_xored_1755007764802_658
);
    // BEGIN: simple_xor_gate_ts1755007764779
    // BEGIN: split_single_stmt_ts1755007764779
    // BEGIN: Mod_BasicOps_ts1755007764786
    logic [7:0] intermediate_arith_ts1755007764784;
    logic [7:0] intermediate_bitwise_ts1755007764784;
    logic [0:0] intermediate_logical_ts1755007764784;
    logic [7:0] intermediate_add_assoc_ts1755007764784;
    logic [7:0] intermediate_mul_assoc_ts1755007764784;
    logic [7:0] intermediate_and_assoc_ts1755007764784;
    logic [7:0] intermediate_or_assoc_ts1755007764784;
    logic [7:0] intermediate_xor_assoc_ts1755007764784;
        // BEGIN: mod_case_block_attrs_ts1755007764797
        logic [3:0] l_temp_ts1755007764797;
            // BEGIN: ContinuousWire_ts1755007764808
            wire internal_w_ts1755007764808;
                // BEGIN: module_conditional_write_ts1755007764814
                cond_if cif_inst();
                always_comb begin
                    if (inj_in2_1755007764779_45) begin
                        cif_inst.control_reg = inj_data_in_1755007764788_778;
                    end else begin
                        cif_inst.control_reg = 16'h0;
                    end
                    inj_control_status_1755007764814_204 = (cif_inst.control_reg != 16'h0);
                end
                // END: module_conditional_write_ts1755007764814

                // BEGIN: reduction_ops_ts1755007764811
                assign inj_out_1755007764811_832 = &intermediate_bitwise_ts1755007764784 | ^intermediate_or_assoc_ts1755007764784;
                // END: reduction_ops_ts1755007764811

            assign internal_w_ts1755007764808 = inj_in1_1755007764779_320;
            assign inj_dout_1755007764808_751       = internal_w_ts1755007764808;
            // END: ContinuousWire_ts1755007764808

            // BEGIN: ReductionOperations_ts1755007764805
            assign inj_and_reduce_1755007764805_65 = &inj_in_q_1755007764779_773;
            assign inj_or_reduce_1755007764805_569 = |inj_in_q_1755007764779_773;
            assign inj_xor_reduce_1755007764805_569 = ^inj_in_q_1755007764779_773;
            // END: ReductionOperations_ts1755007764805

            // BEGIN: more_ops_ts1755007764802
            assign inj_sum_1755007764802_110 = intermediate_bitwise_ts1755007764784 + intermediate_add_assoc_ts1755007764784;
            assign inj_diff_1755007764802_27 = intermediate_bitwise_ts1755007764784 > intermediate_xor_assoc_ts1755007764784;
            assign inj_anded_1755007764802_703 = intermediate_bitwise_ts1755007764784 & intermediate_add_assoc_ts1755007764784;
            assign inj_ored_1755007764802_54 = intermediate_bitwise_ts1755007764784 | intermediate_xor_assoc_ts1755007764784;
            assign inj_xored_1755007764802_658 = intermediate_bitwise_ts1755007764784 ^ intermediate_add_assoc_ts1755007764784;
            // END: more_ops_ts1755007764802

            split_case split_case_inst_1755007764799_7414 (
                .clk_w(clk),
                .d0_w(intermediate_xor_assoc_ts1755007764784),
                .d1_w(intermediate_bitwise_ts1755007764784),
                .d2_w(intermediate_and_assoc_ts1755007764784),
                .d3_w(inj_in_q_1755007764779_773),
                .sel_w(inj_sel_w_1755007764799_734),
                .out_w(inj_out_w_1755007764799_288)
            );
        always_comb begin
            (* full_case *)
            (* parallel_case *)
            case (inj_sel_1755007764790_615)
                2'b00: l_temp_ts1755007764797 = inj_data_in_1755007764790_520;
                2'b01: l_temp_ts1755007764797 = inj_data_in_1755007764790_520 << 1;
                2'b10: l_temp_ts1755007764797 = inj_data_in_1755007764790_520 >> 1;
                default: l_temp_ts1755007764797 = 4'bxxxx;
            endcase
            (* coverage_off *)
            begin : my_named_block
                inj_o_out_1755007764797_76 = l_temp_ts1755007764797;
            end
        end
        // END: mod_case_block_attrs_ts1755007764797

        ModWideBus ModWideBus_inst_1755007764795_2349 (
            .data_in_w(inj_data_in_w_1755007764795_292),
            .data_out_w(inj_data_out_w_1755007764795_797)
        );
        // BEGIN: keyword_import_export_ts1755007764793
        assign inj_keyword_out_1755007764793_199 = inj_in1_1755007764779_320;
        // END: keyword_import_export_ts1755007764793

        module_selection module_selection_inst_1755007764791_4144 (
            .in_bit(clk),
            .in_index(inj_in_index_1755007764791_951),
            .in_part_lsb(inj_sel_1755007764790_615),
            .in_vector(inj_in_const1_1755007764780_772),
            .out_bit_select(inj_out_bit_select_1755007764791_137),
            .out_bitwise_ops(inj_out_bitwise_ops_1755007764791_39),
            .out_part_select(inj_out_part_select_1755007764791_653),
            .out_vector_assign(inj_out_vector_assign_1755007764791_423)
        );
        CaseZExample CaseZExample_inst_1755007764790_5682 (
            .data_in(inj_data_in_1755007764790_520),
            .sel(inj_sel_1755007764790_615),
            .case_out(inj_case_out_1755007764790_549)
        );
        // BEGIN: module_conditional_write_ts1755007764788
        cond_if cif_inst();
        always_comb begin
            if (inj_in1_1755007764779_320) begin
                cif_inst.control_reg = inj_data_in_1755007764788_778;
            end else begin
                cif_inst.control_reg = 16'h0;
            end
            inj_control_status_1755007764788_543 = (cif_inst.control_reg != 16'h0);
        end
        // END: module_conditional_write_ts1755007764788

        mod_basic_bind mod_basic_bind_inst_1755007764787_653 (
            .out1_bind_def(inj_out1_bind_def_1755007764787_749),
            .in1_bind_def(inj_in1_1755007764779_320)
        );
    parameter [7:0] CONST_ZERO = 8'h00;
    always_comb begin
        intermediate_arith_ts1755007764784 = inj_in_a_1755007764780_434;
        intermediate_arith_ts1755007764784 = intermediate_arith_ts1755007764784 + inj_in_b_1755007764780_604;
        intermediate_arith_ts1755007764784 = intermediate_arith_ts1755007764784 - inj_in_c_1755007764780_868;
        intermediate_arith_ts1755007764784 = intermediate_arith_ts1755007764784 * inj_in_const1_1755007764780_772;
        if (inj_in_b_1755007764780_604 != CONST_ZERO) begin
            intermediate_arith_ts1755007764784 = intermediate_arith_ts1755007764784 / inj_in_b_1755007764780_604;
            intermediate_arith_ts1755007764784 = intermediate_arith_ts1755007764784 % inj_in_b_1755007764780_604;
        end else begin
            intermediate_arith_ts1755007764784 = 'x;
        end
        inj_out_arith_1755007764780_94 = intermediate_arith_ts1755007764784;
        intermediate_bitwise_ts1755007764784 = inj_in_a_1755007764780_434;
        intermediate_bitwise_ts1755007764784 = intermediate_bitwise_ts1755007764784 & inj_in_b_1755007764780_604;
        intermediate_bitwise_ts1755007764784 = intermediate_bitwise_ts1755007764784 | inj_in_c_1755007764780_868;
        intermediate_bitwise_ts1755007764784 = intermediate_bitwise_ts1755007764784 ^ inj_in_const1_1755007764780_772;
        inj_out_bitwise_1755007764780_128 = intermediate_bitwise_ts1755007764784;
        intermediate_logical_ts1755007764784 = (inj_in_a_1755007764780_434 != CONST_ZERO) && (inj_in_b_1755007764780_604 != CONST_ZERO);
        intermediate_logical_ts1755007764784 = intermediate_logical_ts1755007764784 || (inj_in_c_1755007764780_868 != CONST_ZERO);
        inj_out_logical_1755007764780_436 = !intermediate_logical_ts1755007764784;
        inj_out_unary_not_1755007764780_824 = ~inj_in_a_1755007764780_434;
        inj_out_negate_1755007764780_915 = -inj_in_a_1755007764780_434;
        intermediate_add_assoc_ts1755007764784 = (inj_in_a_1755007764780_434 + inj_in_b_1755007764780_604) + inj_in_c_1755007764780_868;
        inj_out_add_assoc_1755007764780_935 = intermediate_add_assoc_ts1755007764784;
        intermediate_mul_assoc_ts1755007764784 = (inj_in_a_1755007764780_434 * inj_in_b_1755007764780_604) * inj_in_c_1755007764780_868;
        inj_out_mul_assoc_1755007764780_51 = intermediate_mul_assoc_ts1755007764784;
        intermediate_and_assoc_ts1755007764784 = (inj_in_a_1755007764780_434 & inj_in_b_1755007764780_604) & inj_in_c_1755007764780_868;
        inj_out_and_assoc_1755007764780_785 = intermediate_and_assoc_ts1755007764784;
        intermediate_or_assoc_ts1755007764784 = (inj_in_a_1755007764780_434 | inj_in_b_1755007764780_604) | inj_in_c_1755007764780_868;
        inj_out_or_assoc_1755007764780_236 = intermediate_or_assoc_ts1755007764784;
        intermediate_xor_assoc_ts1755007764784 = (inj_in_a_1755007764780_434 ^ inj_in_b_1755007764780_604) ^ inj_in_c_1755007764780_868;
        inj_out_xor_assoc_1755007764780_155 = intermediate_xor_assoc_ts1755007764784;
        inj_out_and_swap_const_1755007764780_749 = inj_in_const1_1755007764780_772 & inj_in_a_1755007764780_434;
        inj_out_or_swap_not_1755007764780_45 = (~inj_in_a_1755007764780_434) | inj_in_b_1755007764780_604;
        inj_out_xor_swap_var_1755007764780_877 = inj_in_b_1755007764780_604 ^ inj_in_c_1755007764780_868;
    end
    // END: Mod_BasicOps_ts1755007764786

    always @(*) begin
        inj_out_q_1755007764779_742 = inj_in_q_1755007764779_773 + 1;
    end
    // END: split_single_stmt_ts1755007764779

    assign inj_out_1755007764779_560 = inj_in1_1755007764779_320 ^ inj_in2_1755007764779_45;
    // END: simple_xor_gate_ts1755007764779
endmodule

