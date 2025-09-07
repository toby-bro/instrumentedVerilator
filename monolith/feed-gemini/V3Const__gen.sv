module BasicConstOps (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic [7:0] out_add_zero,
    output logic [7:0] out_add_zero_rhs,
    output logic [7:0] out_and_zero_lhs,
    output logic [7:0] out_and_zero_rhs,
    output logic [7:0] out_and_allones_lhs,
    output logic [7:0] out_and_allones_rhs,
    output logic [7:0] out_or_zero_lhs,
    output logic [7:0] out_or_zero_rhs,
    output logic [7:0] out_or_allones_lhs,
    output logic [7:0] out_or_allones_rhs,
    output logic [7:0] out_xor_zero_lhs,
    output logic [7:0] out_xor_zero_rhs,
    output logic [7:0] out_xor_allones_lhs,
    output logic [7:0] out_mul_zero_lhs,
    output logic [7:0] out_mul_zero_rhs,
    output logic [7:0] out_mul_one_lhs,
    output logic [7:0] out_div_zero_lhs,
    output logic [7:0] out_div_one_rhs,
    output logic [7:0] out_sub_zero_lhs,
    output logic [7:0] out_sub_zero_rhs
);
    always_comb begin
        out_add_zero = 8'b0 + in_a;
        out_add_zero_rhs = in_b + 8'b0;
        out_and_zero_lhs = 8'b0 & in_a;
        out_and_zero_rhs = in_b & 8'b0;
        out_and_allones_lhs = 8'hFF & in_a;
        out_and_allones_rhs = in_b & 8'hFF;
        out_or_zero_lhs = 8'b0 | in_a;
        out_or_zero_rhs = in_b | 8'b0;
        out_or_allones_lhs = 8'hFF | in_a;
        out_or_allones_rhs = in_b | 8'hFF;
        out_xor_zero_lhs = 8'b0 ^ in_a;
        out_xor_zero_rhs = in_b ^ 8'b0;
        out_xor_allones_lhs = 8'hFF ^ in_a;
        out_mul_zero_lhs = 8'b0 * in_a;
        out_mul_zero_rhs = in_b * 8'b0;
        out_mul_one_lhs = 8'h01 * in_a;
        out_div_zero_lhs = 8'b0 / in_a;
        out_div_one_rhs = in_b / 8'h01;
        out_sub_zero_lhs = 8'b0 - in_a;
        out_sub_zero_rhs = in_b - 8'b0;
    end
endmodule
module CompareAndLogicalOps (
    input logic in_x,
    input logic in_y,
    input logic signed [7:0] in_s1,
    input logic [7:0] in_u1,
    output logic out_and_same,
    output logic out_or_same,
    output logic out_xor_same,
    output logic out_eq_same,
    output logic out_neq_same,
    output logic out_gt_same,
    output logic out_gte_same,
    output logic out_lt_same,
    output logic out_lte_same,
    output logic [7:0] out_div_same,
    output logic [7:0] out_sub_same,
    output logic out_logand_same,
    output logic out_logor_same,
    output logic out_eq_zero_rhs,
    output logic out_neq_zero_rhs,
    output logic out_logand_neq_zero_lhs,
    output logic out_logand_neq_zero_rhs,
    output logic out_logor_neq_zero_lhs,
    output logic out_logor_neq_zero_rhs,
    output logic out_gte_zero_rhs,
    output logic out_gt_zero_lhs
);
    always_comb begin
        out_and_same = in_x & in_x;
        out_or_same = in_x | in_x;
        out_xor_same = in_x ^ in_x;
        out_eq_same = (in_x == in_x);
        out_neq_same = (in_x != in_x);
        out_gt_same = (in_x > in_x);
        out_gte_same = (in_x >= in_x);
        out_lt_same = (in_x < in_x);
        out_lte_same = (in_x <= in_x);
        out_div_same = (in_u1 / in_u1);
        out_sub_same = (in_u1 - in_u1);
        out_logand_same = in_x && in_x;
        out_logor_same = in_x || in_x;
        out_eq_zero_rhs = (in_x == 1'b0);
        out_neq_zero_rhs = (1'b1 != in_x);
        out_logand_neq_zero_lhs = (1'b1 && in_y);
        out_logand_neq_zero_rhs = (in_x && 1'b1);
        out_logor_neq_zero_lhs = (1'b1 || in_y);
        out_logor_neq_zero_rhs = (in_x || 1'b1);
        out_gte_zero_rhs = (in_s1 >= 8'b0);
        out_gt_zero_lhs = (in_x > 1'b0);
    end
endmodule
module ComplexBooleanAndBitwise (
    input logic cond_in,
    input logic [31:0] val_in_wide,
    input logic [7:0] val_in_small,
    input logic in_bit_a,
    input logic in_bit_b,
    input logic in_bit_c,
    input logic [7:0] in_shift_a,
    input logic [7:0] in_shift_b,
    output logic out_and_cond,
    output logic [7:0] out_masked_or,
    output logic [7:0] out_masked_shift,
    output logic [7:0] out_bitwise_and_shift_same,
    output logic out_or_and_not,
    output logic out_cond_not,
    output logic out_cond_or,
    output logic out_cond_and,
    output logic out_cond_not_or,
    output logic out_cond_not_and,
    output logic out_cond_bool_shift,
    output logic out_lognot_lognot,
    output logic out_lognot_eq,
    output logic out_lognot_lt,
    output logic out_onehot_bit,
    output logic out_onehot0_bit,
    output logic out_logand_bitwise,
    output logic out_logor_bitwise,
    output logic out_lognot_bitwise
);
    always_comb begin
        out_and_cond = 1'b1 & (cond_in ? in_bit_a : in_bit_b);
        out_masked_or = 8'hFF & ((val_in_wide << 8) | (val_in_wide >> 24));
        out_masked_shift = 8'hFF & (val_in_wide >> 24);
        out_bitwise_and_shift_same = (in_shift_a << 2) & (in_shift_b << 2);
        out_or_and_not = in_bit_a | (!in_bit_a & in_bit_b);
        out_cond_not = (!cond_in ? in_bit_a : in_bit_b);
        out_cond_or = (cond_in ? 1'b1 : in_bit_a);
        out_cond_and = (cond_in ? in_bit_a : 1'b0);
        out_cond_not_or = (cond_in ? in_bit_a : 1'b1);
        out_cond_not_and = (cond_in ? 1'b0 : in_bit_a);
        out_cond_bool_shift = ((val_in_small & (in_shift_a >> 4)) ? in_bit_a : in_bit_b);
        out_lognot_lognot = !(!in_bit_a);
        out_lognot_eq = !(in_bit_a == in_bit_b);
        out_lognot_lt = !(in_bit_a < in_bit_b);
        out_onehot_bit = $onehot(in_bit_a);
        out_onehot0_bit = $onehot0(in_bit_a);
        out_logand_bitwise = in_bit_a && in_bit_b;
        out_logor_bitwise = in_bit_a || in_bit_b;
        out_lognot_bitwise = !in_bit_a;
    end
endmodule
module ConcatReplicateOps (
    input logic [7:0] in_c_a,
    input logic [7:0] in_c_b,
    input logic [7:0] in_c_c,
    input logic [31:0] in_c_data,
    output logic [23:0] out_concat_move_nested,
    output logic [15:0] out_concat_zero,
    output logic [15:0] out_concat_adjacent_sel,
    output logic [15:0] out_concat_same,
    output logic [23:0] out_replicate_nested,
    output logic [7:0] out_replicate_one
);
    always_comb begin
        out_concat_move_nested = {{in_c_a, in_c_b}, in_c_c};
        out_concat_zero = {8'b0, in_c_a};
        out_concat_adjacent_sel = {in_c_data[15:8], in_c_data[7:0]};
        out_concat_same = {in_c_a, in_c_a};
        out_replicate_nested = {3{ {2{in_c_a}} }};
        out_replicate_one = {1{in_c_a}};
    end
endmodule
module ShiftExtendWordSelOps (
    input logic [7:0] in_sh_a,
    input logic [15:0] in_sh_b_wide,
    input logic [31:0] in_sh_c_huge,
    input logic [127:0] in_wide_array,
    output logic [7:0] out_shl_zero_lhs,
    output logic [7:0] out_shl_zero_rhs,
    output logic [7:0] out_shl_huge,
    output logic [7:0] out_shl_op_nested,
    output logic [7:0] out_shl_shift_nested,
    output logic [7:0] out_shr_zero_lhs,
    output logic [7:0] out_shr_zero_rhs,
    output logic [7:0] out_shr_huge,
    output logic [7:0] out_shr_op_nested,
    output logic [7:0] out_shr_shift_nested,
    output logic [7:0] out_ext_same_width,
    output logic [23:0] out_ext_nested,
    output logic [63:0] out_word_sel_oob
);
    always_comb begin
        out_shl_zero_lhs = 8'b0 << in_sh_a;
        out_shl_zero_rhs = in_sh_a << 8'b0;
        out_shl_huge = in_sh_a << 32'd256;
        out_shl_op_nested = (in_sh_a & in_sh_b_wide[7:0]) << 2;
        out_shl_shift_nested = (in_sh_a << 2) << 3;
        out_shr_zero_lhs = 8'b0 >> in_sh_a;
        out_shr_zero_rhs = in_sh_a >> 8'b0;
        out_shr_huge = in_sh_a >> 32'd256;
        out_shr_op_nested = (in_sh_a | in_sh_b_wide[7:0]) >> 2;
        out_shr_shift_nested = (in_sh_a >> 2) >> 3;
        out_ext_same_width = in_sh_a;
        out_ext_nested = {16'b0, {8'b0, in_sh_a}};
        out_word_sel_oob = in_wide_array[2];
    end
endmodule
module SelectOps (
    input logic [31:0] in_sel_data,
    input logic [7:0] in_sel_val,
    input logic in_sel_cond,
    output logic [7:0] out_sel_full,
    output logic [7:0] out_sel_extend,
    output logic [7:0] out_sel_nested,
    output logic [3:0] out_sel_bi_lower_add,
    output logic [3:0] out_sel_shift_lower,
    output logic [3:0] out_sel_const,
    output logic [3:0] out_sel_concat,
    output logic [3:0] out_sel_replicate,
    output logic [0:0] out_sel_bufif1,
    output logic [3:0] out_sel_not,
    output logic [3:0] out_sel_and
);
    logic [7:0] z_val;
    logic [23:0] temp_extend_expr;
    logic [15:0] temp_nested_expr;
    logic [7:0] temp_bi_lower_add_expr;
    logic [7:0] temp_shift_lower_expr;
    logic [15:0] temp_concat_expr;
    logic [15:0] temp_replicate_expr;
    logic [7:0] temp_not_expr;
    logic [7:0] temp_and_expr;
    localparam logic [7:0] CONST_FOR_SELECT = 8'hF0;
    assign z_val = 8'bz;
    always_comb begin
        out_sel_full = in_sel_val[7:0];
        temp_extend_expr = {16'b0, in_sel_val};
        out_sel_extend = temp_extend_expr[7:0];
        temp_nested_expr = in_sel_data[15:0];
        out_sel_nested = temp_nested_expr[7:0];
        temp_bi_lower_add_expr = (in_sel_val + in_sel_val);
        out_sel_bi_lower_add = temp_bi_lower_add_expr[3:0];
        temp_shift_lower_expr = (in_sel_data >> 4);
        out_sel_shift_lower = temp_shift_lower_expr[7:4];
        out_sel_const = CONST_FOR_SELECT[7:4];
        temp_concat_expr = ({in_sel_val, in_sel_val});
        out_sel_concat = temp_concat_expr[11:8];
        temp_replicate_expr = ({2{in_sel_val}});
        out_sel_replicate = temp_replicate_expr[11:8];
        out_sel_bufif1 = (in_sel_cond ? in_sel_val[0] : z_val[0]);
        temp_not_expr = (~in_sel_val);
        out_sel_not = temp_not_expr[3:0];
        temp_and_expr = (in_sel_val & in_sel_val);
        out_sel_and = temp_and_expr[3:0];
    end
endmodule
module PowerModuloOps (
    input logic [7:0] base_in,
    input logic [7:0] exp_in,
    output logic [7:0] out_pow_exp_zero,
    output logic [7:0] out_pow_base_two,
    output logic [7:0] out_mod_pow_two
);
    always_comb begin
        out_pow_exp_zero = base_in ** 8'b0;
        out_pow_base_two = 8'h02 ** exp_in;
        out_mod_pow_two = base_in % 8'h04;
    end
endmodule
module LogicalCompareOps (
    input logic in_le_a,
    input logic in_le_b,
    input logic in_li_cond,
    input logic in_li_then,
    input logic in_li_else,
    output logic out_logeq,
    output logic out_logif_cond_zero,
    output logic out_logif_converted
);
    always_comb begin
        out_logeq = (in_le_a == in_le_b);
        out_logif_cond_zero = (1'b0 ? in_li_then : in_li_else);
        out_logif_converted = (in_li_cond ? in_li_then : in_li_else);
    end
endmodule
module SystemFunctions #(
    parameter int UNBOUND_P = 1
) (
    input string in_string_val,
    input logic [7:0] substr_idx_start_val,
    input logic [7:0] substr_idx_len_val,
    output logic out_is_unbounded,
    output logic [31:0] out_substr_n
);
    string local_string;
    always_comb begin
        out_is_unbounded = $isunbounded(UNBOUND_P);
        local_string = "SYSTEMVERILOG";
        out_substr_n = int'(local_string.substr(3, 4));
    end
endmodule
module ReductionOps (
    input logic [31:0] in_red_a,
    input logic [7:0] in_red_b,
    output logic out_redand_bit,
    output logic out_redand_concat,
    output logic out_redand_extend,
    output logic out_redor_bit,
    output logic out_redor_concat,
    output logic out_redor_extend,
    output logic out_redxor_bit,
    output logic out_redxor_concat,
    output logic out_redxor_extend,
    output logic out_redxor_xor_const
);
    always_comb begin
        out_redand_bit = &in_red_b[0];
        out_redand_concat = &{in_red_b[3:0], in_red_b[7:4]};
        out_redand_extend = &({32'b0, in_red_b});
        out_redor_bit = |in_red_b[0];
        out_redor_concat = |{in_red_b[3:0], in_red_b[7:4]};
        out_redor_extend = |({32'b0, in_red_b});
        out_redxor_bit = ^in_red_b[0];
        out_redxor_concat = ^{in_red_b[3:0], in_red_b[7:4]};
        out_redxor_extend = ^({32'b0, in_red_b});
        out_redxor_xor_const = ^(in_red_b ^ 8'hAA);
    end
endmodule
module DisplayAndString (
    input logic in_disp_val,
    output logic [7:0] out_dummy
);
    string s1;
    string s2;
    string s_combined;
    always_comb begin
        out_dummy = 8'h0;
        s1 = $sformatf("Value: %0d", 10);
        s2 = $sformatf("Another value: %0h", 8'hFF);
        s_combined = $sformatf("Combined: %0d %0h", 20, 8'hAA);
        s1 = $sformatf("This is a constant string.");
    end
endmodule
module ConditionalAndNotPush (
    input logic a_in,
    input logic b_in,
    input logic c_in,
    output logic out_cond_short_circuit_false,
    output logic out_cond_short_circuit_true,
    output logic out_not_pushed_through
);
    always_comb begin
        out_cond_short_circuit_false = (1'b0 ? a_in : b_in);
        out_cond_short_circuit_true = (1'b1 ? a_in : b_in);
        out_not_pushed_through = !((a_in == b_in) == c_in);
    end
endmodule
module ParameterGenerateSim #(
    parameter int PARAM_WIDTH = 8,
    parameter int OOB_PARAM_INDEX = 7
) (
    input logic [7:0] in_val,
    output logic [7:0] out_param_width_use,
    output logic out_oob_select_warn,
    output logic out_always_false_loop_warn,
    output logic out_infinite_loop_warn
);
    generate
        if (1'b0) begin : gen_if_false
            assign out_always_false_loop_warn = 1'b0;
        end
        else begin : gen_if_true
            assign out_always_false_loop_warn = 1'b1;
        end
    endgenerate
    always_comb begin
        out_param_width_use = in_val[PARAM_WIDTH-1:0];
        out_oob_select_warn = in_val[OOB_PARAM_INDEX];
        out_infinite_loop_warn = 1'b0;
    end
endmodule
module ReleaseStatementOps (
    input logic in_r_a,
    input logic in_r_b,
    output logic out_r_dummy
);
    logic var_to_release_a;
    logic var_to_release_b;
    always_comb begin
        out_r_dummy = in_r_a;
        force var_to_release_a = in_r_a;
        force var_to_release_b = in_r_b;
        release {var_to_release_a, var_to_release_b};
    end
endmodule
module ArrayAndAssignOps (
    input logic [7:0] in_arr_idx,
    input logic [7:0] in_arr_val,
    input logic in_arr_sel_val,
    output logic [7:0] out_array_access,
    output logic out_assign_self,
    output logic [1:0] out_multi_assign
);
    localparam logic [7:0] my_array [0:15] = '{default: 8'h00};
    logic [7:0] self_loop_var;
    logic bit_val_a, bit_val_b;
    always_comb begin
        out_array_access = my_array[in_arr_idx];
        self_loop_var = self_loop_var;
        out_assign_self = self_loop_var[0];
        bit_val_a = in_arr_sel_val;
        bit_val_b = in_arr_sel_val;
        out_multi_assign[0] = bit_val_a;
        out_multi_assign[1] = bit_val_b;
    end
endmodule
