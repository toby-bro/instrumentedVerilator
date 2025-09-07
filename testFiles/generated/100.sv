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

module typedef_struct_public_mod (
    input logic [15:0] packed_in,
    output logic [7:0] field2_o
);
    typedef struct packed {
        logic [7:0] field1;
        logic [7:0] field2;
    } my_public_packed_struct_t;
    my_public_packed_struct_t my_struct_var;
    always_comb begin
        my_struct_var = packed_in;
    end
    assign field2_o = my_struct_var.field2;
endmodule

module snippet (
    input wire clk,
    input wire [7:0] inj_in_a_1755007786028_271,
    input wire [7:0] inj_in_b_1755007786028_728,
    input wire inj_in_bit_1755007786028_441,
    input wire [7:0] inj_in_c_1755007786028_861,
    input wire inj_in_cond_neq_rhs_1755007786028_243,
    input wire inj_in_cond_not_1755007786028_246,
    input wire [7:0] inj_in_not_else_1755007786028_723,
    input wire [7:0] inj_in_not_then_1755007786028_165,
    input logic inj_in_p_1755007786027_223,
    input logic inj_in_q_1755007786027_530,
    input logic [7:0] inj_in_val_a_l_1755007786027_902,
    input logic [7:0] inj_in_val_b_l_1755007786027_756,
    input logic [15:0] inj_packed_in_1755007786027_659,
    input wire reset,
    output logic [7:0] inj_field2_o_1755007786027_17,
    output logic inj_o_sum_1755007786028_30,
    output logic inj_out_eq_1755007786028_53,
    output logic inj_out_eq_concat_1755007786028_468,
    output logic inj_out_gt_1755007786028_857,
    output logic inj_out_gte_1755007786028_1,
    output logic inj_out_lt_1755007786028_248,
    output logic inj_out_lte_1755007786028_915,
    output logic inj_out_neq_1755007786028_389,
    output logic inj_out_not_eq_1755007786028_14,
    output logic inj_out_not_neq_1755007786028_159,
    output logic inj_out_r_1755007786027_792,
    output logic inj_out_ternary_1755007786028_784,
    output logic inj_out_ternary_1bit_0else_1755007786028_221,
    output logic inj_out_ternary_1bit_0then_1755007786028_320,
    output logic inj_out_ternary_1bit_1else_1755007786028_16,
    output logic inj_out_ternary_1bit_1then_1755007786028_895,
    output logic inj_out_ternary_const_cond_false_1755007786028_905,
    output logic inj_out_ternary_const_cond_true_1755007786028_964,
    output logic [7:0] inj_out_ternary_dec_1755007786028_92,
    output logic [7:0] inj_out_ternary_inc_1755007786028_482,
    output logic [7:0] inj_out_ternary_pulled_nots_1755007786028_601,
    output logic inj_out_ternary_swapped_cond_1755007786028_795,
    output logic inj_out_ternary_swapped_neq_cond_1755007786028_914,
    output logic [8:0] inj_out_val_c_l_1755007786027_704,
    output logic [7:0] inj_out_val_d_l_1755007786027_613,
    output logic [7:0] inj_wide_reg_1755007786028_86
);
    // BEGIN: split_inputs_outputs_only_ts1755007786027
    // BEGIN: LintSensitiveList_ts1755007786027
    // BEGIN: mod_lint_target_ts1755007786028
    logic l_reg_ts1755007786028;
    always_comb begin
        l_reg_ts1755007786028 = 1;
        inj_wide_reg_1755007786028_86 = {clk, inj_in_cond_not_1755007786028_246};
    end
    assign inj_o_sum_1755007786028_30 = clk + inj_in_cond_not_1755007786028_246;
    // END: mod_lint_target_ts1755007786028

    Mod_TernaryLogic Mod_TernaryLogic_inst_1755007786028_736 (
        .in_cond(clk),
        .out_ternary_swapped_neq_cond(inj_out_ternary_swapped_neq_cond_1755007786028_914),
        .out_eq(inj_out_eq_1755007786028_53),
        .out_eq_concat(inj_out_eq_concat_1755007786028_468),
        .in_cond_neq_rhs(inj_in_cond_neq_rhs_1755007786028_243),
        .out_ternary_1bit_0then(inj_out_ternary_1bit_0then_1755007786028_320),
        .out_ternary_inc(inj_out_ternary_inc_1755007786028_482),
        .out_lt(inj_out_lt_1755007786028_248),
        .out_not_neq(inj_out_not_neq_1755007786028_159),
        .out_ternary(inj_out_ternary_1755007786028_784),
        .out_gte(inj_out_gte_1755007786028_1),
        .out_not_eq(inj_out_not_eq_1755007786028_14),
        .in_b(inj_in_b_1755007786028_728),
        .out_ternary_1bit_0else(inj_out_ternary_1bit_0else_1755007786028_221),
        .in_cond_not(inj_in_cond_not_1755007786028_246),
        .out_ternary_1bit_1then(inj_out_ternary_1bit_1then_1755007786028_895),
        .in_not_then(inj_in_not_then_1755007786028_165),
        .out_ternary_pulled_nots(inj_out_ternary_pulled_nots_1755007786028_601),
        .in_not_else(inj_in_not_else_1755007786028_723),
        .out_ternary_const_cond_true(inj_out_ternary_const_cond_true_1755007786028_964),
        .in_a(inj_in_a_1755007786028_271),
        .out_ternary_const_cond_false(inj_out_ternary_const_cond_false_1755007786028_905),
        .out_lte(inj_out_lte_1755007786028_915),
        .out_gt(inj_out_gt_1755007786028_857),
        .in_cond_neq_lhs(reset),
        .in_bit(inj_in_bit_1755007786028_441),
        .out_neq(inj_out_neq_1755007786028_389),
        .in_c(inj_in_c_1755007786028_861),
        .out_ternary_dec(inj_out_ternary_dec_1755007786028_92),
        .out_ternary_swapped_cond(inj_out_ternary_swapped_cond_1755007786028_795),
        .out_ternary_1bit_1else(inj_out_ternary_1bit_1else_1755007786028_16)
    );
    typedef_struct_public_mod typedef_struct_public_mod_inst_1755007786027_5989 (
        .packed_in(inj_packed_in_1755007786027_659),
        .field2_o(inj_field2_o_1755007786027_17)
    );
    always_comb begin
        inj_out_r_1755007786027_792 = inj_in_p_1755007786027_223 | inj_in_q_1755007786027_530;
    end
    // END: LintSensitiveList_ts1755007786027

    always @(*) begin
        inj_out_val_c_l_1755007786027_704 = inj_in_val_a_l_1755007786027_902 + inj_in_val_b_l_1755007786027_756;
        inj_out_val_d_l_1755007786027_613 = inj_in_val_a_l_1755007786027_902 - inj_in_val_b_l_1755007786027_756;
    end
    // END: split_inputs_outputs_only_ts1755007786027
endmodule

