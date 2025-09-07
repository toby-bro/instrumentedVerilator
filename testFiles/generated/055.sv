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
    input wire [7:0] inj_in_a_1755007770032_649,
    input wire [7:0] inj_in_b_1755007770032_555,
    input wire [7:0] inj_in_c_1755007770032_909,
    input wire inj_in_cond_neq_lhs_1755007770032_235,
    input wire inj_in_cond_neq_rhs_1755007770032_843,
    input wire inj_in_cond_not_1755007770032_976,
    input wire [7:0] inj_in_not_else_1755007770032_635,
    input wire [7:0] inj_in_not_then_1755007770032_647,
    input logic [31:0] inj_in_val_1755007770032_263,
    input bit inj_select_a_1755007770032_66,
    input wire reset,
    output logic inj_out_eq_1755007770032_215,
    output logic inj_out_eq_concat_1755007770032_946,
    output logic inj_out_gt_1755007770032_172,
    output logic inj_out_gte_1755007770032_169,
    output logic inj_out_lt_1755007770032_777,
    output logic inj_out_lte_1755007770032_572,
    output logic inj_out_neq_1755007770032_568,
    output logic inj_out_not_eq_1755007770032_546,
    output logic inj_out_not_neq_1755007770032_281,
    output logic inj_out_ternary_1755007770032_330,
    output logic inj_out_ternary_1bit_0else_1755007770032_496,
    output logic inj_out_ternary_1bit_0then_1755007770032_401,
    output logic inj_out_ternary_1bit_1else_1755007770032_483,
    output logic inj_out_ternary_1bit_1then_1755007770032_831,
    output logic inj_out_ternary_const_cond_false_1755007770032_766,
    output logic inj_out_ternary_const_cond_true_1755007770032_190,
    output logic [7:0] inj_out_ternary_dec_1755007770032_942,
    output logic [7:0] inj_out_ternary_inc_1755007770032_509,
    output logic [7:0] inj_out_ternary_pulled_nots_1755007770032_836,
    output logic inj_out_ternary_swapped_cond_1755007770032_109,
    output logic inj_out_ternary_swapped_neq_cond_1755007770032_72,
    output logic [31:0] inj_out_val_1755007770032_41
);
    // BEGIN: member_access_packed_union_ts1755007770032
    typedef union packed {
        logic [31:0] a_ts1755007770032; 
        logic [31:0] b_ts1755007770032; 
    } my_packed_union;
    my_packed_union union_var;
    Mod_TernaryLogic Mod_TernaryLogic_inst_1755007770032_9785 (
        .out_lte(inj_out_lte_1755007770032_572),
        .in_cond(clk),
        .out_ternary_inc(inj_out_ternary_inc_1755007770032_509),
        .out_ternary_pulled_nots(inj_out_ternary_pulled_nots_1755007770032_836),
        .out_neq(inj_out_neq_1755007770032_568),
        .out_ternary_1bit_0else(inj_out_ternary_1bit_0else_1755007770032_496),
        .out_eq(inj_out_eq_1755007770032_215),
        .out_not_eq(inj_out_not_eq_1755007770032_546),
        .out_ternary_swapped_cond(inj_out_ternary_swapped_cond_1755007770032_109),
        .out_gt(inj_out_gt_1755007770032_172),
        .in_cond_neq_lhs(inj_in_cond_neq_lhs_1755007770032_235),
        .out_ternary_swapped_neq_cond(inj_out_ternary_swapped_neq_cond_1755007770032_72),
        .out_ternary(inj_out_ternary_1755007770032_330),
        .out_gte(inj_out_gte_1755007770032_169),
        .out_eq_concat(inj_out_eq_concat_1755007770032_946),
        .out_not_neq(inj_out_not_neq_1755007770032_281),
        .out_ternary_dec(inj_out_ternary_dec_1755007770032_942),
        .in_b(inj_in_b_1755007770032_555),
        .in_c(inj_in_c_1755007770032_909),
        .in_bit(reset),
        .out_ternary_const_cond_true(inj_out_ternary_const_cond_true_1755007770032_190),
        .in_not_else(inj_in_not_else_1755007770032_635),
        .in_cond_not(inj_in_cond_not_1755007770032_976),
        .out_ternary_1bit_0then(inj_out_ternary_1bit_0then_1755007770032_401),
        .out_ternary_1bit_1then(inj_out_ternary_1bit_1then_1755007770032_831),
        .in_not_then(inj_in_not_then_1755007770032_647),
        .out_lt(inj_out_lt_1755007770032_777),
        .in_cond_neq_rhs(inj_in_cond_neq_rhs_1755007770032_843),
        .in_a(inj_in_a_1755007770032_649),
        .out_ternary_const_cond_false(inj_out_ternary_const_cond_false_1755007770032_766),
        .out_ternary_1bit_1else(inj_out_ternary_1bit_1else_1755007770032_483)
    );
    always_comb begin
        if (inj_select_a_1755007770032_66)
            union_var.a_ts1755007770032 = inj_in_val_1755007770032_263;
        else
            union_var.b_ts1755007770032 = inj_in_val_1755007770032_263[31:0];
        inj_out_val_1755007770032_41 = union_var.a_ts1755007770032;
    end
    // END: member_access_packed_union_ts1755007770032
endmodule

