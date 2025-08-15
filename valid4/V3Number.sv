module IntegerOps(
    input  logic [31:0] in_a,
    input  logic [31:0] in_b,
    input  logic [63:0] in_long_val,
    output logic [31:0] out_neg_a,
    output logic [31:0] out_add,
    output logic [31:0] out_sub,
    output logic [31:0] out_mul,
    output logic [31:0] out_div,
    output logic [31:0] out_mod,
    output logic [63:0] out_assign_long,
    output logic [7:0] out_lit_8h,
    output logic [15:0] out_lit_16d,
    output logic [3:0] out_lit_4o,
    output logic [7:0] out_lit_8b,
    output logic [0:0] out_lit_unsized_0,
    output logic [0:0] out_lit_unsized_1,
    output logic [0:0] out_lit_unsized_x,
    output logic [0:0] out_lit_unsized_z,
    output logic signed [7:0] out_lit_8sd,
    output logic [7:0] out_trunc_warning,
    output logic [7:0] out_warn_literal_trunc
);
    localparam logic [8:0] WIDE_LITERAL_TO_TRUNCATE = 9'b1_0000_0000;
    always_comb begin
        out_neg_a = -in_a;
        out_add = in_a + in_b;
        out_sub = in_a - in_b;
        out_mul = in_a * in_b;
        out_div = in_a / 32'b0;
        out_mod = in_a % 32'b0;
        out_assign_long = in_long_val;
        out_lit_8h = 8'hA5;
        out_lit_16d = 16'd12345;
        out_lit_4o = 4'o7;
        out_lit_8b = 8'b1010_1101;
        out_lit_unsized_0 = '0;
        out_lit_unsized_1 = '1;
        out_lit_unsized_x = 'x;
        out_lit_unsized_z = 'z;
        out_lit_8sd = -8'd5;
        out_trunc_warning = WIDE_LITERAL_TO_TRUNCATE;
        out_warn_literal_trunc = 8'd300;
    end
endmodule
module SignedPowerOps(
    input  logic signed [31:0] in_sa,
    input  logic signed [31:0] in_sb,
    input  logic [7:0] in_exp,
    output logic signed [31:0] out_mul_s,
    output logic signed [31:0] out_div_s,
    output logic signed [31:0] out_mod_s,
    output logic [31:0] out_pow_uu,
    output logic signed [31:0] out_pow_su,
    output logic signed [31:0] out_pow_ss,
    output logic [31:0] out_pow_us
);
    always_comb begin
        out_mul_s = in_sa * in_sb;
        out_div_s = in_sa / 32'sb0;
        out_mod_s = in_sa % 32'sb0;
        out_pow_uu = in_sa[31:0] ** in_exp;
        out_pow_su = in_sa ** in_exp;
        out_pow_ss = in_sa ** in_sb;
        out_pow_us = in_sa[31:0] ** in_sb;
    end
endmodule
module BitwiseLogicalOps(
    input  logic [7:0] in_val1,
    input  logic [7:0] in_val2,
    input  logic [7:0] in_val_xz1,
    output logic [7:0] out_not,
    output logic [7:0] out_and,
    output logic [7:0] out_or,
    output logic [7:0] out_xor,
    output logic out_log_not,
    output logic out_log_and,
    output logic out_log_or,
    output logic out_log_if,
    output logic out_red_or,
    output logic out_red_and,
    output logic out_red_xor
);
    always_comb begin
        out_not = ~in_val1;
        out_and = in_val1 & in_val2;
        out_or = in_val1 | in_val2;
        out_xor = in_val1 ^ in_val2;
        out_log_not = !in_val1;
        out_log_and = in_val1 && in_val2;
        out_log_or = in_val1 || in_val2;
        out_log_if = in_val1 -> in_val2;
        out_red_or = |in_val_xz1;
        out_red_and = &in_val_xz1;
        out_red_xor = ^in_val_xz1;
    end
endmodule
module ComparisonShiftOps(
    input  logic [15:0] in_c1,
    input  logic [15:0] in_c2,
    input  logic signed [15:0] in_sc1,
    input  logic signed [15:0] in_sc2,
    input  logic [15:0] in_w_c1,
    input  logic [3:0] in_shift_amount,
    output logic out_eq,
    output logic out_neq,
    output logic out_case_eq,
    output logic out_case_neq,
    output logic out_wild_eq,
    output logic out_wild_neq,
    output logic out_gt,
    output logic out_gt_s,
    output logic out_gte,
    output logic out_gte_s,
    output logic out_lt,
    output logic out_lte,
    output logic out_lt_s,
    output logic out_lte_s,
    output logic [15:0] out_sh_r,
    output logic [15:0] out_sh_rs,
    output logic [15:0] out_sh_l
);
    always_comb begin
        out_eq = (in_c1 == in_c2);
        out_neq = (in_c1 != in_c2);
        out_case_eq = (in_c1 === in_c2);
        out_case_neq = (in_c1 !== in_c2);
        out_wild_eq = (in_w_c1 ==? 16'b01x1z01x_01z1x01x);
        out_wild_neq = (in_w_c1 !=? 16'b01x1z01x_01z1x01x);
        out_gt = (in_c1 > in_c2);
        out_gt_s = (in_sc1 > in_sc2);
        out_gte = (in_c1 >= in_c2);
        out_gte_s = (in_sc1 >= in_sc2);
        out_lt = (in_c1 < in_c2);
        out_lte = (in_c1 <= in_c2);
        out_lt_s = (in_sc1 < in_sc2);
        out_lte_s = (in_sc1 <= in_sc2);
        out_sh_r = in_c1 >> in_shift_amount;
        out_sh_rs = in_sc1 >>> in_shift_amount;
        out_sh_l = in_c1 << in_shift_amount;
    end
endmodule
module AdvancedBitOps(
    input  logic [31:0] in_data,
    input  logic [31:0] in_data_xz,
    input  logic [7:0] in_rep_val,
    input  logic [3:0] in_sel_msb_idx,
    input  logic [3:0] in_sel_lsb_idx,
    input  logic [3:0] in_sel_into_lsb_idx,
    input  logic [3:0] in_sel_into_width,
    input  logic [63:0] in_clog2_input,
    output logic [7:0] out_concat_val,
    output logic [31:0] out_replicated_val,
    output logic [7:0] out_selected_val,
    output logic [31:0] out_sel_into_val,
    output logic [31:0] out_extend_s,
    output logic [31:0] out_extend_xz,
    output logic [31:0] out_masked_val,
    output logic out_is_all_x,
    output logic out_is_eq_zero,
    output logic out_is_neq_zero,
    output logic out_is_eq_one,
    output logic out_is_eq_all_ones,
    output logic out_is_four_state,
    output logic out_is_any_x,
    output logic out_is_any_z,
    output logic out_is_any_xz,
    output logic [6:0] out_clog2_res,
    output logic [5:0] out_count_ones,
    output logic [6:0] out_most_set_bit_p1,
    output logic out_is_unknown,
    output logic out_onehot,
    output logic out_onehot0,
    output logic [5:0] out_count_bits_0,
    output logic [5:0] out_count_bits_1,
    output logic [5:0] out_count_bits_multi_ctrl
);
    logic [31:0] local_concat_a = 32'h0000_1234;
    logic [31:0] local_concat_b = 32'h5678_9ABC;
    logic [7:0] local_sel_base = 8'hF0;
    logic [31:0] local_target_sel_into;
    logic signed [7:0] local_ext_val_s = 8'sb1000_0000;
    logic [7:0] local_ext_val_xz = 8'b1011_01xz;
    always_comb begin
        out_concat_val = {local_concat_a[7:0], local_concat_b[7:0]};
        out_replicated_val = {4{in_rep_val}};
        out_selected_val = local_sel_base[in_sel_msb_idx : in_sel_lsb_idx];
        local_target_sel_into = in_data;
        local_target_sel_into[in_sel_into_lsb_idx +: in_sel_into_width] = {in_sel_into_width{1'b1}};
        out_sel_into_val = local_target_sel_into;
        out_extend_s = {{24{local_ext_val_s[7]}}, local_ext_val_s};
        out_extend_xz = {{24{local_ext_val_xz[7]}}, local_ext_val_xz};
        out_masked_val = in_data & (32'hFFFF_FFFF >> 16);
        out_is_all_x = (in_data_xz == 32'hXXXXXXXX);
        out_is_eq_zero = (in_data == 32'b0);
        out_is_neq_zero = (in_data != 32'b0);
        out_is_eq_one = (in_data == 32'b1);
        out_is_eq_all_ones = (in_data == 32'hFFFF_FFFF);
        out_is_four_state = in_data_xz.is_x() || in_data_xz.is_z();
        out_is_any_x = in_data_xz.is_x();
        out_is_any_z = in_data_xz.is_z();
        out_is_any_xz = in_data_xz.is_x() || in_data_xz.is_z();
        out_clog2_res = $clog2(in_clog2_input);
        out_count_ones = $countones(in_data);
        out_most_set_bit_p1 = $clog2(in_data + 1);
        out_is_unknown = $isunknown(in_data);
        out_onehot = $onehot(in_data);
        out_onehot0 = $onehot0(in_data);
        out_count_bits_0 = $countbits(in_data, 1'b0);
        out_count_bits_1 = $countbits(in_data, 1'b1);
        out_count_bits_multi_ctrl = $countbits(in_data, 1'b0, 1'b1, 1'bX);
    end
endmodule
module StringOps(
    input  string in_str1,
    input  string in_str2,
    input  int in_char_idx,
    input  logic [7:0] in_char_val_in,
    input  int in_sub_idx_i,
    input  int in_sub_idx_j,
    input  bit in_compare_case_ignore,
    input  string in_atoi_str,
    input  string in_atof_str,
    output int out_len,
    output string out_putc_res,
    output string out_substr_res,
    output string out_repl_res,
    output string out_lower_res,
    output string out_upper_res,
    output bit out_str_eq,
    output bit out_str_neq,
    output bit out_str_gt,
    output bit out_str_gte,
    output bit out_str_lt,
    output bit out_str_lte,
    output logic [7:0] out_getc_res,
    output int out_compare_nn,
    output int out_atoi_res,
    output real out_atof_res
);
    string local_putc_str;
    always_comb begin
        out_len = in_str1.len();
        local_putc_str = in_str1;
        if (in_char_idx >= 0 && in_char_idx < local_putc_str.len() && in_char_val_in != 0) begin
            local_putc_str = local_putc_str.putc(in_char_idx, in_char_val_in);
        end else begin
            local_putc_str = in_str1.putc(in_char_idx, 0);
        end
        out_putc_res = local_putc_str;
        out_getc_res = in_str1.getc(in_char_idx);
        out_substr_res = in_str1.substr(in_sub_idx_i, in_sub_idx_j);
        out_repl_res = {2{in_str1}};
        out_lower_res = in_str1.tolower();
        out_upper_res = in_str1.toupper();
        out_str_eq = (in_str1 == in_str2);
        out_str_neq = (in_str1 != in_str2);
        out_str_gt = (in_str1 > in_str2);
        out_str_gte = (in_str1 >= in_str2);
        out_str_lt = (in_str1 < in_str2);
        out_str_lte = (in_str1 <= in_str2);
        out_compare_nn = in_str1.compare(in_str2, in_compare_case_ignore);
        out_atoi_res = $atoi(in_atoi_str);
        out_atof_res = $atof(in_atof_str);
    end
endmodule
module RealNumberOps(
    input  real in_r1,
    input  real in_r2,
    input  logic signed [31:0] in_i_to_r_val,
    input  logic [63:0] in_bits_to_r_val,
    output real out_neg_r,
    output real out_add_r,
    output real out_sub_r,
    output real out_mul_r,
    output real out_div_r,
    output real out_pow_r,
    output real out_i_to_r,
    output logic signed [31:0] out_r_to_i_trunc,
    output logic signed [31:0] out_r_to_i_round,
    output real out_bits_to_r,
    output logic [63:0] out_real_to_bits,
    output bit out_eq_r,
    output bit out_neq_r,
    output bit out_gt_r,
    output bit out_gte_r,
    output bit out_lt_r,
    output bit out_lte_r
);
    always_comb begin
        out_neg_r = -in_r1;
        out_add_r = in_r1 + in_r2;
        out_sub_r = in_r1 - in_r2;
        out_mul_r = in_r1 * in_r2;
        out_div_r = in_r1 / in_r2;
        out_pow_r = in_r1 ** in_r2;
        out_i_to_r = real'(in_i_to_r_val);
        out_r_to_i_trunc = int'(in_r1);
        out_r_to_i_round = $round(in_r1);
        out_real_to_bits = $realtobits(in_r1);
        out_bits_to_r = $bitstoreal(in_bits_to_r_val);
        out_eq_r = (in_r1 == in_r2);
        out_neq_r = (in_r1 != in_r2);
        out_gt_r = (in_r1 > in_r2);
        out_gte_r = (in_r1 >= in_r2);
        out_lt_r = (in_r1 < in_r2);
        out_lte_r = (in_r1 <= in_r2);
    end
endmodule
module FourStateOps(
    input  logic [7:0] in_logic_val_xz,
    input  logic [7:0] in_logic_val_01,
    output logic [7:0] out_buf_if1_res,
    output logic [15:0] out_x_extend_val,
    output logic [15:0] out_z_extend_val,
    output logic [7:0] out_all_bits_0,
    output logic [7:0] out_all_bits_1,
    output logic [7:0] out_all_bits_x,
    output logic [7:0] out_all_bits_z,
    output logic [7:0] out_all_bits_x_removed,
    output logic [7:0] out_value_1,
    output logic [7:0] out_bit_x0_test
);
    logic [7:0] local_x_removed_val;
    logic [7:0] temp_all_0;
    logic [7:0] temp_all_1;
    logic [7:0] temp_all_x;
    logic [7:0] temp_all_z;
    logic [7:0] temp_value_1;
    always_comb begin
        out_buf_if1_res = in_logic_val_01 ? in_logic_val_xz : 8'hZZ;
        out_x_extend_val = {{8{1'bx}}, in_logic_val_xz};
        out_z_extend_val = {{8{1'bz}}, in_logic_val_xz};
        temp_all_0 = '0;
        out_all_bits_0 = temp_all_0;
        temp_all_1 = '1;
        out_all_bits_1 = temp_all_1;
        temp_all_x = 'x;
        out_all_bits_x = temp_all_x;
        temp_all_z = 'z;
        out_all_bits_z = temp_all_z;
        local_x_removed_val = 8'bx / 8'bx;
        out_all_bits_x_removed = local_x_removed_val;
        temp_value_1 = 8'd1;
        out_value_1 = temp_value_1;
        out_bit_x0_test = in_logic_val_01;
        out_bit_x0_test[0] = in_logic_val_01[0];
        out_bit_x0_test[7] = in_logic_val_xz[7];
    end
endmodule
module LargeWidthOps(
    input  logic [127:0] in_large_a,
    input  logic [127:0] in_large_b,
    input  logic [127:0] in_large_c_xz,
    output logic [127:0] out_large_add,
    output logic [127:0] out_large_mul,
    output logic [127:0] out_large_div,
    output logic [127:0] out_large_mod,
    output logic [127:0] out_large_and_xz,
    output logic [127:0] out_large_or_xz,
    output logic [127:0] out_large_shift_r,
    output logic [127:0] out_large_shift_l,
    output logic [127:0] out_large_negate,
    output logic out_large_is_eq_zero,
    output logic out_large_is_all_x
);
    always_comb begin
        out_large_add = in_large_a + in_large_b;
        out_large_mul = in_large_a * in_large_b;
        out_large_div = in_large_a / 128'b0;
        out_large_mod = in_large_a % 128'b0;
        out_large_and_xz = in_large_a & in_large_c_xz;
        out_large_or_xz = in_large_a | in_large_c_xz;
        out_large_shift_r = in_large_a >> 65;
        out_large_shift_l = in_large_a << 65;
        out_large_negate = -in_large_a;
        out_large_is_eq_zero = (in_large_a == 128'h0);
        out_large_is_all_x = (in_large_c_xz == 128'hXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX);
    end
endmodule
