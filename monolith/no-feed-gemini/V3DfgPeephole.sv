module UnaryOptimizations (
    input  logic [7:0] in_val_extend,
    input  logic [15:0] in_val_negate,
    input  logic [0:0] in_val_log_not,
    input  logic [7:0] in_val_not,
    input  logic [7:0] in_val_not_not_src,
    input  logic [7:0] in_eq_a,
    input  logic [7:0] in_eq_b,
    input  logic [7:0] in_neq_a,
    input  logic [7:0] in_neq_b,
    input  logic        cond_not_push,
    input  logic [7:0] then_not_push,
    input  logic [7:0] else_not_push,
    output logic [15:0] out_extend,
    output logic [15:0] out_negate,
    output logic [0:0] out_log_not,
    output logic [7:0] out_not,
    output logic [7:0] out_not_not,
    output logic [0:0] out_not_eq,
    output logic [0:0] out_not_neq,
    output logic [7:0] out_not_cond_push
);
    assign out_extend = {{8{1'b0}}, in_val_extend};
    assign out_negate = -in_val_negate;
    assign out_log_not = !in_val_log_not;
    assign out_not = ~in_val_not;
    assign out_not_not = ~(~in_val_not_not_src);
    assign out_not_eq = ~(in_eq_a == in_eq_b);
    assign out_not_neq = ~(in_neq_a != in_neq_b);
    assign out_not_cond_push = cond_not_push ? ~then_not_push : ~else_not_push;
endmodule
module ReductionOptimizations (
    input  logic [15:0] in_red_or,
    input  logic [15:0] in_red_and,
    input  logic [15:0] in_red_xor,
    input  logic [0:0] in_red_1bit,
    input  logic        cond_red_const,
    input  logic [7:0] then_red_const,
    input  logic [15:0] in_red_concat_lhs,
    input  logic [15:0] in_red_bitwise_a,
    input  logic [15:0] in_red_bitwise_b,
    output logic [0:0] out_red_or,
    output logic [0:0] out_red_and,
    output logic [0:0] out_red_xor,
    output logic [0:0] out_red_1bit,
    output logic [0:0] out_red_cond,
    output logic [0:0] out_red_concat_or,
    output logic [0:0] out_red_concat_and,
    output logic [0:0] out_red_bitwise_or_and,
    output logic [0:0] out_red_bitwise_and_or
);
    assign out_red_or = |in_red_or;
    assign out_red_and = &in_red_and;
    assign out_red_xor = ^in_red_xor;
    assign out_red_1bit = |in_red_1bit;
    assign out_red_cond = |(cond_red_const ? then_red_const : 8'hAA);
    assign out_red_concat_or = |{in_red_concat_lhs, 16'hFFFF};
    assign out_red_concat_and = &{in_red_concat_lhs, 16'h0000};
    assign out_red_bitwise_or_and = (|in_red_bitwise_a) & (|in_red_bitwise_b);
    assign out_red_bitwise_and_or = (&in_red_bitwise_a) | (&in_red_bitwise_b);
endmodule
module SelectOptimizations (
    input  logic [31:0] in_sel_full_width,
    input  logic [31:0] in_sel_concat_lhs,
    input  logic [31:0] in_sel_concat_rhs,
    input  logic [7:0]  in_sel_repl_src,
    input  logic [15:0] in_sel_not_src,
    input  logic [31:0] in_sel_sel_src,
    input  logic        cond_sel,
    input  logic [15:0] then_sel_cond,
    input  logic [15:0] else_sel_cond,
    input  logic [15:0] in_shift_l_src,
    output logic [31:0] out_sel_full_width,
    output logic [15:0] out_sel_concat_rhs,
    output logic [15:0] out_sel_concat_lhs,
    output logic [10:0] out_sel_concat_straddle,
    output logic [7:0]  out_sel_repl,
    output logic [15:0] out_sel_not,
    output logic [7:0]  out_sel_sel,
    output logic [15:0] out_sel_cond,
    output logic [7:0]  out_sel_shift_l
);
    logic [31:0] concat_for_straddle;
    assign out_sel_full_width = in_sel_full_width[31:0];
    assign out_sel_concat_rhs = {in_sel_concat_lhs, in_sel_concat_rhs}[15:0];
    assign out_sel_concat_lhs = {in_sel_concat_lhs, in_sel_concat_rhs}[31:16];
    assign concat_for_straddle = {in_sel_concat_lhs, in_sel_concat_rhs};
    assign out_sel_concat_straddle = concat_for_straddle[20:10];
    assign out_sel_repl = ({4{in_sel_repl_src}})[7:0];
    assign out_sel_not = (~in_sel_not_src)[15:0];
    assign out_sel_sel = (in_sel_sel_src[15:0])[7:0];
    assign out_sel_cond = (cond_sel ? then_sel_cond : else_sel_cond)[15:0];
    assign out_sel_shift_l = (in_shift_l_src << 4)[7:0];
endmodule
module BitwiseOptimizations (
    input  logic [7:0] in_bit_a,
    input  logic [7:0] in_bit_b,
    input  logic [7:0] in_bit_self,
    input  logic [7:0] in_bit_not_a_src,
    input  logic [7:0] in_bit_not_b_src,
    input  logic [7:0] in_bit_neq_b,
    input  logic [7:0] in_bit_neq_c,
    input  logic [7:0] in_const_for_swap,
    input  logic [7:0] in_not_for_swap,
    input  logic [7:0] in_var_B_for_swap,
    input  logic [7:0] in_var_A_for_swap,
    input  logic [7:0] in_assoc_A,
    input  logic [7:0] in_assoc_B,
    input  logic [7:0] in_assoc_C,
    input  logic [15:0] in_push_concat_val,
    input  logic [15:0] in_push_concat_const,
    input  logic [7:0] in_dist_A,
    input  logic [7:0] in_dist_B,
    input  logic [7:0] in_dist_C,
    output logic [7:0] out_and_basic,
    output logic [7:0] out_and_self,
    output logic [7:0] out_and_zero,
    output logic [7:0] out_and_ones,
    output logic [7:0] out_and_contradictory_2,
    output logic [7:0] out_and_contradictory_3,
    output logic [7:0] out_and_de_morgan_not_not,
    output logic [7:0] out_and_de_morgan_not_neq,
    output logic [7:0] out_or_basic,
    output logic [7:0] out_or_self,
    output logic [7:0] out_or_zero,
    output logic [7:0] out_or_ones,
    output logic [7:0] out_or_tautological_2,
    output logic [7:0] out_or_tautological_3,
    output logic [7:0] out_or_de_morgan_not_not,
    output logic [7:0] out_or_de_morgan_not_neq,
    output logic [7:0] out_or_concat_zero_lhs_rhs,
    output logic [7:0] out_or_concat_lhs_zero_rhs,
    output logic [7:0] out_xor_basic,
    output logic [7:0] out_xor_self,
    output logic [7:0] out_xor_zero,
    output logic [7:0] out_xor_ones,
    output logic [7:0] out_and_const_swap,
    output logic [7:0] out_and_not_swap,
    output logic [7:0] out_and_var_swap,
    output logic [7:0] out_and_assoc_right_leaning,
    output logic [7:0] out_or_const_swap,
    output logic [7:0] out_or_not_swap,
    output logic [7:0] out_or_var_swap,
    output logic [7:0] out_or_assoc_right_leaning,
    output logic [7:0] out_xor_const_swap,
    output logic [7:0] out_xor_not_swap,
    output logic [7:0] out_xor_var_swap,
    output logic [7:0] out_xor_assoc_right_leaning,
    output logic [15:0] out_and_push_concat,
    output logic [15:0] out_or_push_concat,
    output logic [15:0] out_xor_push_concat,
    output logic [7:0] out_distributive_and_or
);
    assign out_and_basic = in_bit_a & in_bit_b;
    assign out_and_self = in_bit_self & in_bit_self;
    assign out_and_zero = 8'h00 & in_bit_a;
    assign out_and_ones = 8'hFF & in_bit_a;
    assign out_and_contradictory_2 = (~in_bit_not_a_src) & in_bit_not_a_src;
    assign out_and_contradictory_3 = (~in_bit_not_a_src) & (in_bit_not_a_src & in_bit_b);
    assign out_and_de_morgan_not_not = (~in_bit_not_a_src) & (~in_bit_not_b_src);
    assign out_and_de_morgan_not_neq = (~in_bit_not_a_src) & (in_bit_neq_b != in_bit_neq_c);
    assign out_or_basic = in_bit_a | in_bit_b;
    assign out_or_self = in_bit_self | in_bit_self;
    assign out_or_zero = 8'h00 | in_bit_a;
    assign out_or_ones = 8'hFF | in_bit_a;
    assign out_or_tautological_2 = (~in_bit_not_a_src) | in_bit_not_a_src;
    assign out_or_tautological_3 = (~in_bit_not_a_src) | (in_bit_not_a_src | in_bit_b);
    assign out_or_de_morgan_not_not = (~in_bit_not_a_src) | (~in_bit_not_b_src);
    assign out_or_de_morgan_not_neq = (~in_bit_not_a_src) | (in_bit_neq_b != in_bit_neq_c);
    assign out_or_concat_zero_lhs_rhs = {4'b0, in_bit_a[3:0]} | {in_bit_b[3:0], 4'b0};
    assign out_or_concat_lhs_zero_rhs = {in_bit_a[3:0], 4'b0} | {4'b0, in_bit_b[3:0]};
    assign out_xor_basic = in_bit_a ^ in_bit_b;
    assign out_xor_self = in_bit_self ^ in_bit_self;
    assign out_xor_zero = 8'h00 ^ in_bit_a;
    assign out_xor_ones = 8'hFF ^ in_bit_a;
    assign out_and_const_swap = in_bit_a & in_const_for_swap;
    assign out_and_not_swap = in_bit_a & (~in_not_for_swap);
    assign out_and_var_swap = in_var_B_for_swap & in_var_A_for_swap;
    assign out_and_assoc_right_leaning = (in_assoc_A & in_assoc_B) & in_assoc_C;
    assign out_or_const_swap = in_bit_a | in_const_for_swap;
    assign out_or_not_swap = in_bit_a | (~in_not_for_swap);
    assign out_or_var_swap = in_var_B_for_swap | in_var_A_for_swap;
    assign out_or_assoc_right_leaning = (in_assoc_A | in_assoc_B) | in_assoc_C;
    assign out_xor_const_swap = in_bit_a ^ in_const_for_swap;
    assign out_xor_not_swap = in_bit_a ^ (~in_not_for_swap);
    assign out_xor_var_swap = in_var_B_for_swap ^ in_var_A_for_swap;
    assign out_xor_assoc_right_leaning = (in_assoc_A ^ in_assoc_B) ^ in_assoc_C;
    assign out_and_push_concat = in_push_concat_const & {in_push_concat_val[15:8], in_push_concat_val[7:0]};
    assign out_or_push_concat = in_push_concat_const | {in_push_concat_val[15:8], in_push_concat_val[7:0]};
    assign out_xor_push_concat = in_push_concat_const ^ {in_push_concat_val[15:8], in_push_concat_val[7:0]};
    assign out_distributive_and_or = (in_dist_A | in_dist_B) & (in_dist_A | in_dist_C);
endmodule
module ArithmeticOptimizations (
    input  logic [15:0] in_add_a,
    input  logic [15:0] in_add_b,
    input  logic [15:0] in_add_c,
    input  logic [15:0] in_mul_a,
    input  logic [15:0] in_mul_b,
    input  logic [15:0] in_mul_c,
    input  logic [15:0] in_sub_a,
    input  logic [15:0] in_sub_b,
    input  logic [15:0] in_div_a,
    input  logic [15:0] in_div_b,
    input  logic [15:0] in_mod_a,
    input  logic [15:0] in_mod_b,
    input  logic [15:0] in_shift_l_val,
    input  logic [3:0]  in_shift_amt_l,
    input  logic [15:0] in_shift_r_val,
    input  logic [3:0]  in_shift_amt_r,
    input  logic [7:0]  in_repl_once_src,
    input  logic [0:0]  in_sub_1bit_src,
    output logic [15:0] out_add,
    output logic [15:0] out_mul,
    output logic [15:0] out_sub,
    output logic [15:0] out_div,
    output logic [15:0] out_mod,
    output logic [15:0] out_shift_l,
    output logic [15:0] out_shift_r,
    output logic [7:0]  out_repl_once,
    output logic [15:0] out_sub_zero,
    output logic [0:0]  out_sub_1bit_not,
    output logic [15:0] out_add_assoc_right_leaning,
    output logic [15:0] out_mul_assoc_right_leaning,
    output logic [15:0] out_add_const_swap,
    output logic [15:0] out_mul_const_swap,
    output logic [15:0] out_shift_l_rhs_zero_ext,
    output logic [15:0] out_shift_r_rhs_zero_ext
);
    assign out_add = in_add_a + in_add_b;
    assign out_mul = in_mul_a * in_mul_b;
    assign out_sub = in_sub_a - in_sub_b;
    assign out_div = in_div_a / in_div_b;
    assign out_mod = in_mod_a % in_mod_b;
    assign out_shift_l = in_shift_l_val << in_shift_amt_l;
    assign out_shift_r = in_shift_r_val >> in_shift_amt_r;
    assign out_repl_once = {1{in_repl_once_src}};
    assign out_sub_zero = in_sub_a - 16'h0000;
    assign out_sub_1bit_not = in_sub_1bit_src - 1'b1;
    assign out_add_assoc_right_leaning = (in_add_a + in_add_b) + in_add_c;
    assign out_mul_assoc_right_leaning = (in_mul_a * in_mul_b) * in_mul_c;
    assign out_add_const_swap = 16'h0001 + in_add_a;
    assign out_mul_const_swap = 16'h0002 * in_mul_a;
    assign out_shift_l_rhs_zero_ext = in_shift_l_val << {12'b0, in_shift_amt_l};
    assign out_shift_r_rhs_zero_ext = in_shift_r_val >> {12'b0, in_shift_amt_r};
endmodule
module ComparisonOptimizations (
    input  logic [7:0] in_comp_a,
    input  logic [7:0] in_comp_b,
    input  logic [7:0] in_comp_c,
    input  logic [15:0] in_comp_concat_val,
    input  logic [15:0] in_comp_concat_const,
    output logic [0:0] out_eq,
    output logic [0:0] out_neq,
    output logic [0:0] out_gt,
    output logic [0:0] out_gte,
    output logic [0:0] out_lt,
    output logic [0:0] out_lte,
    output logic [0:0] out_eq_const_swap,
    output logic [0:0] out_eq_concat_push
);
    assign out_eq = in_comp_a == in_comp_b;
    assign out_neq = in_comp_a != in_comp_b;
    assign out_gt = in_comp_a > in_comp_b;
    assign out_gte = in_comp_a >= in_comp_b;
    assign out_lt = in_comp_a < in_comp_b;
    assign out_lte = in_comp_a <= in_comp_b;
    assign out_eq_const_swap = in_comp_a == in_comp_c;
    assign out_eq_concat_push = in_comp_concat_const == {in_comp_concat_val[15:8], in_comp_concat_val[7:0]};
endmodule
module LogicalOptimizations (
    input  logic        in_log_cond,
    input  logic        in_log_expr,
    input  logic [7:0]  in_log_val_a,
    input  logic [7:0]  in_log_val_b,
    input  logic [7:0]  in_log_then,
    input  logic [7:0]  in_log_else,
    input  logic [0:0]  in_log_1bit_a,
    input  logic [0:0]  in_log_1bit_b,
    output logic [0:0] out_log_and,
    output logic [0:0] out_log_or,
    output logic [0:0] out_log_eq,
    output logic [7:0] out_log_if,
    output logic [0:0] out_log_and_1bit,
    output logic [0:0] out_log_or_1bit
);
    assign out_log_and = in_log_cond && in_log_expr;
    assign out_log_or = in_log_cond || in_log_expr;
    assign out_log_eq = in_log_val_a == in_log_val_b;
    assign out_log_if = in_log_cond ? in_log_then : in_log_else;
    assign out_log_and_1bit = in_log_1bit_a && in_log_1bit_b;
    assign out_log_or_1bit = in_log_1bit_a || in_log_1bit_b;
endmodule
module ConcatOptimizations (
    input  logic [7:0] in_cat_a,
    input  logic [7:0] in_cat_b,
    input  logic [7:0] in_cat_c,
    input  logic [15:0] in_cat_sel_src,
    input  logic [7:0] in_cat_not_a,
    input  logic [7:0] in_cat_not_b,
    input  logic [31:0] in_cat_adjoin_src,
    output logic [15:0] out_cat_basic,
    output logic [23:0] out_cat_assoc_right_leaning,
    output logic [15:0] out_cat_zero_and_sel_top,
    output logic [15:0] out_cat_sel_bottom_and_zero,
    output logic [15:0] out_cat_push_not,
    output logic [15:0] out_cat_adjoining_sels_1,
    output logic [23:0] out_cat_adjoining_sels_2,
    output logic [23:0] out_cat_adjoining_sels_3
);
    assign out_cat_basic = {in_cat_a, in_cat_b};
    assign out_cat_assoc_right_leaning = {{in_cat_a, in_cat_b}, in_cat_c};
    assign out_cat_zero_and_sel_top = {8'h00, in_cat_sel_src[7:0]};
    assign out_cat_sel_bottom_and_zero = {in_cat_sel_src[7:0], 8'h00};
    assign out_cat_push_not = {~in_cat_not_a, ~in_cat_not_b};
    assign out_cat_adjoining_sels_1 = {in_cat_adjoin_src[15:8], in_cat_adjoin_src[7:0]};
    assign out_cat_adjoining_sels_2 = {{in_cat_adjoin_src[23:16], in_cat_adjoin_src[15:8]}, in_cat_c};
    assign out_cat_adjoining_sels_3 = {in_cat_a, {in_cat_adjoin_src[15:8], in_cat_adjoin_src[7:0]}};
endmodule
module ConditionalOptimizations (
    input  logic        in_cond_true_false_c,
    input  logic [7:0]  in_cond_a,
    input  logic [7:0]  in_cond_b,
    input  logic [7:0]  in_cond_same_val,
    input  logic        in_cond_same_c,
    input  logic        in_cond_neg_c,
    input  logic [7:0]  in_cond_neg_then,
    input  logic [7:0]  in_cond_neg_else,
    input  logic [7:0]  in_cond_neq_a,
    input  logic [7:0]  in_cond_neq_b,
    input  logic [7:0]  in_cond_neq_then,
    input  logic [7:0]  in_cond_neq_else,
    input  logic        in_cond_pull_not_c,
    input  logic [7:0]  in_cond_pull_not_t,
    input  logic [7:0]  in_cond_pull_not_e,
    input  logic        in_cond_or_a,
    input  logic        in_cond_or_b,
    input  logic [7:0]  in_cond_or_x,
    input  logic [7:0]  in_cond_or_y,
    input  logic [7:0]  in_cond_or_z,
    input  logic [7:0]  in_cond_inc_a,
    input  logic        in_cond_inc_c,
    input  logic [7:0]  in_cond_dec_a,
    input  logic        in_cond_dec_c,
    input  logic        in_cond_bit_c,
    input  logic        in_cond_bit_a,
    input  logic        in_cond_bit_b,
    output logic [7:0] out_cond_true,
    output logic [7:0] out_cond_false,
    output logic [7:0] out_cond_same_branches,
    output logic [7:0] out_cond_neg_swap,
    output logic [7:0] out_cond_neq_swap,
    output logic [7:0] out_cond_pull_nots,
    output logic [7:0] out_cond_or_then_cond,
    output logic [7:0] out_cond_inc,
    output logic [7:0] out_cond_dec,
    output logic [0:0] out_cond_bit_0_then,
    output logic [0:0] out_cond_bit_cond_then,
    output logic [0:0] out_cond_bit_1_then,
    output logic [0:0] out_cond_bit_0_else,
    output logic [0:0] out_cond_bit_1_else
);
    assign out_cond_true = 1'b1 ? in_cond_a : in_cond_b;
    assign out_cond_false = 1'b0 ? in_cond_a : in_cond_b;
    assign out_cond_same_branches = in_cond_same_c ? in_cond_same_val : in_cond_same_val;
    assign out_cond_neg_swap = !in_cond_neg_c ? in_cond_neg_then : in_cond_neg_else;
    assign out_cond_neq_swap = (in_cond_neq_a != in_cond_neq_b) ? in_cond_neq_then : in_cond_neq_else;
    assign out_cond_pull_nots = in_cond_pull_not_c ? (~in_cond_pull_not_t) : (~in_cond_pull_not_e);
    assign out_cond_or_then_cond = (in_cond_or_a || in_cond_or_b) ? (in_cond_or_a ? in_cond_or_x : in_cond_or_y) : in_cond_or_z;
    assign out_cond_inc = in_cond_inc_c ? (in_cond_inc_a + 8'h1) : in_cond_inc_a;
    assign out_cond_dec = in_cond_dec_c ? (in_cond_dec_a - 8'h1) : in_cond_dec_a;
    assign out_cond_bit_0_then = in_cond_bit_c ? 1'b0 : in_cond_bit_b;
    assign out_cond_bit_cond_then = in_cond_bit_c ? in_cond_bit_c : in_cond_bit_b;
    assign out_cond_bit_1_then = in_cond_bit_c ? 1'b1 : in_cond_bit_b;
    assign out_cond_bit_0_else = in_cond_bit_c ? in_cond_bit_a : 1'b0;
    assign out_cond_bit_1_else = in_cond_bit_c ? in_cond_bit_a : 1'b1;
endmodule
module ArraySelectOptimization (
    input  logic [7:0] array_val_0,
    input  logic [7:0] array_val_1,
    input  logic [7:0] array_val_2,
    input  logic [7:0] array_val_3,
    input  logic [1:0] index_const_0,
    input  logic [1:0] index_const_1,
    output logic [7:0] out_array_sel_0,
    output logic [7:0] out_array_sel_1
);
    logic [31:0] my_packed_array;
    assign my_packed_array = {array_val_3, array_val_2, array_val_1, array_val_0};
    assign out_array_sel_0 = my_packed_array[index_const_0 * 8 +: 8];
    assign out_array_sel_1 = my_packed_array[index_const_1 * 8 +: 8];
endmodule
