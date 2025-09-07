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

module snippet (
    input wire clk,
    input wire [7:0] inj_in_a_1755007851862_515,
    input wire [7:0] inj_in_b_1755007851862_124,
    input wire [7:0] inj_in_c_1755007851862_879,
    input wire inj_in_cond_1755007851862_547,
    input wire inj_in_cond_neq_rhs_1755007851862_788,
    input wire inj_in_cond_not_1755007851862_456,
    input wire [7:0] inj_in_not_else_1755007851862_400,
    input wire [7:0] inj_in_not_then_1755007851862_986,
    input wire reset,
    output logic inj_out_eq_1755007851862_101,
    output logic inj_out_eq_concat_1755007851862_55,
    output logic inj_out_gt_1755007851862_79,
    output logic inj_out_gte_1755007851862_216,
    output logic inj_out_lt_1755007851862_32,
    output logic inj_out_lte_1755007851862_644,
    output logic inj_out_neq_1755007851862_334,
    output logic inj_out_not_eq_1755007851862_563,
    output logic inj_out_not_neq_1755007851862_250,
    output logic inj_out_ternary_1755007851862_280,
    output logic inj_out_ternary_1bit_0else_1755007851862_601,
    output logic inj_out_ternary_1bit_0then_1755007851862_38,
    output logic inj_out_ternary_1bit_1else_1755007851862_421,
    output logic inj_out_ternary_1bit_1then_1755007851862_110,
    output logic inj_out_ternary_const_cond_false_1755007851862_459,
    output logic inj_out_ternary_const_cond_true_1755007851862_442,
    output logic [7:0] inj_out_ternary_dec_1755007851862_717,
    output logic [7:0] inj_out_ternary_inc_1755007851862_526,
    output logic [7:0] inj_out_ternary_pulled_nots_1755007851862_87,
    output logic inj_out_ternary_swapped_cond_1755007851862_111,
    output logic inj_out_ternary_swapped_neq_cond_1755007851862_766
);
    Mod_TernaryLogic Mod_TernaryLogic_inst_1755007851862_9992 (
        .in_bit(reset),
        .out_ternary_1bit_0then(inj_out_ternary_1bit_0then_1755007851862_38),
        .out_not_neq(inj_out_not_neq_1755007851862_250),
        .out_ternary(inj_out_ternary_1755007851862_280),
        .out_ternary_inc(inj_out_ternary_inc_1755007851862_526),
        .in_not_then(inj_in_not_then_1755007851862_986),
        .in_a(inj_in_a_1755007851862_515),
        .out_gte(inj_out_gte_1755007851862_216),
        .out_eq(inj_out_eq_1755007851862_101),
        .out_ternary_const_cond_false(inj_out_ternary_const_cond_false_1755007851862_459),
        .in_cond(inj_in_cond_1755007851862_547),
        .out_neq(inj_out_neq_1755007851862_334),
        .in_b(inj_in_b_1755007851862_124),
        .in_not_else(inj_in_not_else_1755007851862_400),
        .out_not_eq(inj_out_not_eq_1755007851862_563),
        .out_ternary_swapped_neq_cond(inj_out_ternary_swapped_neq_cond_1755007851862_766),
        .out_ternary_1bit_1then(inj_out_ternary_1bit_1then_1755007851862_110),
        .out_lte(inj_out_lte_1755007851862_644),
        .out_eq_concat(inj_out_eq_concat_1755007851862_55),
        .out_ternary_1bit_1else(inj_out_ternary_1bit_1else_1755007851862_421),
        .out_ternary_pulled_nots(inj_out_ternary_pulled_nots_1755007851862_87),
        .in_cond_neq_lhs(clk),
        .in_c(inj_in_c_1755007851862_879),
        .out_ternary_dec(inj_out_ternary_dec_1755007851862_717),
        .in_cond_not(inj_in_cond_not_1755007851862_456),
        .out_gt(inj_out_gt_1755007851862_79),
        .out_ternary_const_cond_true(inj_out_ternary_const_cond_true_1755007851862_442),
        .out_lt(inj_out_lt_1755007851862_32),
        .in_cond_neq_rhs(inj_in_cond_neq_rhs_1755007851862_788),
        .out_ternary_1bit_0else(inj_out_ternary_1bit_0else_1755007851862_601),
        .out_ternary_swapped_cond(inj_out_ternary_swapped_cond_1755007851862_111)
    );
endmodule

