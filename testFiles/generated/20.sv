module LogicDependencyChain (
    input logic clk,
    input logic d_in,
    output logic q_out
);
    logic q1, q2;
    always @(posedge clk) begin
        q1 <= d_in;
    end
    always @(q1) begin
        q2 = ~q1;
    end
    assign q_out = q2;
endmodule

module Mod_TernaryLogic (
    input wire [7:0] in_a,
    input wire [7:0] in_b,
    input wire in_bit,
    input wire [7:0] in_c,
    input wire in_cond,
    input wire in_cond_neq_lhs,
    input wire in_cond_neq_rhs,
    input wire in_cond_not,
    input wire [7:0] in_not_else,
    input wire [7:0] in_not_then,
    output logic out_eq,
    output logic out_eq_concat,
    output logic out_gt,
    output logic out_gte,
    output logic out_lt,
    output logic out_lte,
    output logic out_neq,
    output logic out_not_eq,
    output logic out_not_neq,
    output logic out_ternary,
    output logic out_ternary_1bit_0else,
    output logic out_ternary_1bit_0then,
    output logic out_ternary_1bit_1else,
    output logic out_ternary_1bit_1then,
    output logic out_ternary_const_cond_false,
    output logic out_ternary_const_cond_true,
    output logic [7:0] out_ternary_dec,
    output logic [7:0] out_ternary_inc,
    output logic [7:0] out_ternary_pulled_nots,
    output logic out_ternary_swapped_cond,
    output logic out_ternary_swapped_neq_cond
);
    parameter [7:0] CONST_ONE_8 = 8'h01;
    parameter [0:0] CONST_ZERO_1 = 1'b0;
    parameter [0:0] CONST_ONE_1 = 1'b1;
    logic [7:0] intermediate_const_concat_comp;
    logic [15:0] intermediate_concat_comp_src;
    always_comb begin
        out_eq = (in_a == in_b);
        out_neq = (in_a != in_b);
        out_gt = (in_a > in_b);
        out_lt = (in_a < in_b);
        out_gte = (in_a >= in_b);
        out_lte = (in_a <= in_b);
        out_not_eq = !(in_a == in_b);
        out_not_neq = !(in_a != in_b);
        intermediate_const_concat_comp = 8'hAA;
        intermediate_concat_comp_src = {in_a, in_b};
        out_eq_concat = (intermediate_const_concat_comp == intermediate_concat_comp_src[7:0]);
        out_ternary = in_cond ? in_a[0] : in_b[0];
        out_ternary_const_cond_true = 1'b1 ? in_a[0] : in_b[0];
        out_ternary_const_cond_false = 1'b0 ? in_a[0] : in_b[0];
        out_ternary_swapped_cond = !in_cond_not ? in_a[0] : in_b[0];
        out_ternary_swapped_neq_cond = (in_cond_neq_lhs != in_cond_neq_rhs) ? in_a[0] : in_b[0];
        out_ternary_pulled_nots = in_cond ? ~in_not_then : ~in_not_else;
        out_ternary_inc = in_cond ? (in_a + CONST_ONE_8) : in_a;
        out_ternary_dec = in_cond ? (in_a - CONST_ONE_8) : in_a;
        out_ternary_1bit_0then = in_cond ? CONST_ZERO_1 : in_bit;
        out_ternary_1bit_1then = in_cond ? CONST_ONE_1 : in_bit;
        out_ternary_1bit_0else = in_cond ? in_bit : CONST_ZERO_1;
        out_ternary_1bit_1else = in_cond ? in_bit : CONST_ONE_1;
    end
endmodule

module Module_BasicSyntax (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic out_cmp,
    output logic [7:0] out_ops
);
    logic [7:0] temp;
    always_comb begin
        temp = in_a + in_b;
    end
    assign out_ops = (in_a & in_b) | (in_a ^ in_b);
    assign out_cmp = (in_a == in_b);
endmodule

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module snippet (
    input wire clk,
    input int inj_b_1755004209732_940,
    input logic [31:0] inj_data_in_1755004209745_773,
    input logic [7:0] inj_i3_r_1755004209742_356,
    input logic [3:0] inj_i_bind_control_1755004209739_169,
    input wire [7:0] inj_in_a_1755004209735_232,
    input wire [7:0] inj_in_b_1755004209735_186,
    input wire [7:0] inj_in_c_1755004209735_570,
    input wire inj_in_cond_1755004209735_315,
    input wire inj_in_cond_neq_lhs_1755004209735_227,
    input wire inj_in_cond_not_1755004209735_624,
    input bit [3:0] inj_in_data_1755004209737_536,
    input wire [7:0] inj_in_not_else_1755004209735_531,
    input wire [7:0] inj_in_not_then_1755004209735_774,
    input logic [7:0] inj_in_val_h_1755004209731_678,
    input logic [4:0] inj_start_bit_1755004209745_877,
    input wire reset,
    output logic inj_bit_out_1755004209745_3,
    output logic [7:0] inj_byte_out_1755004209745_823,
    output logic [7:0] inj_o1_r_1755004209742_77,
    output logic [7:0] inj_o2_r_1755004209742_404,
    output logic [7:0] inj_o3_r_1755004209742_49,
    output logic inj_o_bind_status_1755004209739_150,
    output logic inj_o_sum_1755004209731_799,
    output logic inj_out_a_1755004209732_359,
    output int inj_out_b_1755004209732_819,
    output logic inj_out_cmp_1755004209734_918,
    output logic inj_out_eq_1755004209735_783,
    output logic inj_out_eq_concat_1755004209735_338,
    output logic inj_out_gt_1755004209735_182,
    output logic inj_out_gte_1755004209735_210,
    output logic inj_out_lt_1755004209735_500,
    output logic inj_out_lte_1755004209735_848,
    output logic inj_out_neq_1755004209735_2,
    output logic inj_out_not_eq_1755004209735_240,
    output logic inj_out_not_neq_1755004209735_413,
    output logic [7:0] inj_out_ops_1755004209734_613,
    output logic [7:0] inj_out_reg_h_1755004209731_351,
    output bit [3:0] inj_out_result_1755004209737_19,
    output logic inj_out_ternary_1755004209735_680,
    output logic inj_out_ternary_1bit_0else_1755004209735_301,
    output logic inj_out_ternary_1bit_0then_1755004209735_80,
    output logic inj_out_ternary_1bit_1else_1755004209735_951,
    output logic inj_out_ternary_1bit_1then_1755004209735_410,
    output logic inj_out_ternary_const_cond_false_1755004209735_205,
    output logic inj_out_ternary_const_cond_true_1755004209735_233,
    output logic [7:0] inj_out_ternary_dec_1755004209735_554,
    output logic [7:0] inj_out_ternary_inc_1755004209735_712,
    output logic [7:0] inj_out_ternary_pulled_nots_1755004209735_490,
    output logic inj_out_ternary_swapped_cond_1755004209735_970,
    output logic inj_out_ternary_swapped_neq_cond_1755004209735_181,
    output logic [7:0] inj_out_val_c_1755004209733_233,
    output logic inj_q_out_1755004209732_942,
    output logic [7:0] inj_wide_reg_1755004209731_546
);
    // BEGIN: mod_lint_target_ts1755004209731
    logic l_reg_ts1755004209731;
        // BEGIN: ModuleBasic_ts1755004209732
        parameter int P1  = 10;
        localparam int LP1 = 20;
        logic c_ts1755004209732;
        int   d_ts1755004209732;
        always_comb begin
            logic temp_v_ts1755004209732;
                // BEGIN: split_seq_dependency_ts1755004209733
                logic [7:0] mid_val_c_ts1755004209733;
                    // BEGIN: split_complex_blocking_ts1755004209742
                    logic [7:0] t1_r_ts1755004209742, t2_r_ts1755004209742;
                        // BEGIN: ArrayIndexAndPartSelect_ts1755004209745
                        logic [31:0] internal_data = inj_data_in_1755004209745_773;
                        assign inj_bit_out_1755004209745_3 = internal_data[d_ts1755004209732];
                        assign inj_byte_out_1755004209745_823 = internal_data[inj_start_bit_1755004209745_877 +: 8];
                        // END: ArrayIndexAndPartSelect_ts1755004209745

                    always @(*) begin
                        t1_r_ts1755004209742 = mid_val_c_ts1755004209733 + inj_in_val_h_1755004209731_678;
                        inj_o1_r_1755004209742_77 = t1_r_ts1755004209742 - inj_i3_r_1755004209742_356;
                        t2_r_ts1755004209742 = inj_in_val_h_1755004209731_678 * inj_i3_r_1755004209742_356;
                        inj_o2_r_1755004209742_404 = t1_r_ts1755004209742 + t2_r_ts1755004209742;
                        inj_o3_r_1755004209742_49 = t2_r_ts1755004209742 / 2;
                    end
                    // END: split_complex_blocking_ts1755004209742

                    module_to_bind module_to_bind_inst_1755004209739_1600 (
                        .o_bind_status(inj_o_bind_status_1755004209739_150),
                        .i_bind_clk(clk),
                        .i_bind_control(inj_i_bind_control_1755004209739_169)
                    );
                    // BEGIN: mod_if_else_simple_ts1755004209737
                always_comb begin
                    if (inj_in_data_1755004209737_536 > 8) begin
                        inj_out_result_1755004209737_19 = inj_in_data_1755004209737_536 + 1;
                    end else begin
                        inj_out_result_1755004209737_19 = inj_in_data_1755004209737_536 - 1;
                    end
                end
                    // END: mod_if_else_simple_ts1755004209737

                    Mod_TernaryLogic Mod_TernaryLogic_inst_1755004209735_8989 (
                        .out_ternary_const_cond_false(inj_out_ternary_const_cond_false_1755004209735_205),
                        .out_ternary_1bit_0then(inj_out_ternary_1bit_0then_1755004209735_80),
                        .out_lte(inj_out_lte_1755004209735_848),
                        .in_not_then(inj_in_not_then_1755004209735_774),
                        .out_not_eq(inj_out_not_eq_1755004209735_240),
                        .in_cond_neq_rhs(clk),
                        .in_cond(inj_in_cond_1755004209735_315),
                        .out_ternary_swapped_cond(inj_out_ternary_swapped_cond_1755004209735_970),
                        .out_eq(inj_out_eq_1755004209735_783),
                        .out_gte(inj_out_gte_1755004209735_210),
                        .out_ternary_pulled_nots(inj_out_ternary_pulled_nots_1755004209735_490),
                        .out_ternary_dec(inj_out_ternary_dec_1755004209735_554),
                        .out_ternary_swapped_neq_cond(inj_out_ternary_swapped_neq_cond_1755004209735_181),
                        .in_bit(reset),
                        .out_not_neq(inj_out_not_neq_1755004209735_413),
                        .out_ternary_inc(inj_out_ternary_inc_1755004209735_712),
                        .out_ternary_const_cond_true(inj_out_ternary_const_cond_true_1755004209735_233),
                        .out_ternary_1bit_1then(inj_out_ternary_1bit_1then_1755004209735_410),
                        .out_ternary_1bit_0else(inj_out_ternary_1bit_0else_1755004209735_301),
                        .in_b(inj_in_b_1755004209735_186),
                        .out_lt(inj_out_lt_1755004209735_500),
                        .out_gt(inj_out_gt_1755004209735_182),
                        .out_ternary_1bit_1else(inj_out_ternary_1bit_1else_1755004209735_951),
                        .in_c(inj_in_c_1755004209735_570),
                        .in_a(inj_in_a_1755004209735_232),
                        .in_cond_not(inj_in_cond_not_1755004209735_624),
                        .out_neq(inj_out_neq_1755004209735_2),
                        .out_ternary(inj_out_ternary_1755004209735_680),
                        .in_not_else(inj_in_not_else_1755004209735_531),
                        .in_cond_neq_lhs(inj_in_cond_neq_lhs_1755004209735_227),
                        .out_eq_concat(inj_out_eq_concat_1755004209735_338)
                    );
                    Module_BasicSyntax Module_BasicSyntax_inst_1755004209734_8119 (
                        .out_cmp(inj_out_cmp_1755004209734_918),
                        .out_ops(inj_out_ops_1755004209734_613),
                        .in_a(mid_val_c_ts1755004209733),
                        .in_b(inj_in_val_h_1755004209731_678)
                    );
                always @(posedge clk) begin
                    mid_val_c_ts1755004209733 <= inj_in_val_h_1755004209731_678 + 1;
                    inj_out_val_c_1755004209733_233 <= mid_val_c_ts1755004209733 * 2;
                end
                // END: split_seq_dependency_ts1755004209733

            temp_v_ts1755004209732 = d_ts1755004209732;
            c_ts1755004209732      = temp_v_ts1755004209732;
        end
        assign inj_out_a_1755004209732_359 = l_reg_ts1755004209731;
        assign d_ts1755004209732     = inj_b_1755004209732_940;
        assign inj_out_b_1755004209732_819 = d_ts1755004209732 + P1 + LP1;
        // END: ModuleBasic_ts1755004209732

        LogicDependencyChain LogicDependencyChain_inst_1755004209732_9711 (
            .d_in(l_reg_ts1755004209731),
            .q_out(inj_q_out_1755004209732_942),
            .clk(clk)
        );
        // BEGIN: split_if_only_then_ts1755004209732
        always @(posedge clk) begin
            if (l_reg_ts1755004209731) begin
                inj_out_reg_h_1755004209731_351 <= inj_in_val_h_1755004209731_678;
            end
        end
        // END: split_if_only_then_ts1755004209732

    always_comb begin
        l_reg_ts1755004209731 = 1;
        inj_wide_reg_1755004209731_546 = {clk, reset};
    end
    assign inj_o_sum_1755004209731_799 = clk + reset;
    // END: mod_lint_target_ts1755004209731
endmodule

