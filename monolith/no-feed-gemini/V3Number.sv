module LogicAndArithmeticOps(
    input logic [127:0] in_a,
    input logic [127:0] in_b,
    input logic [127:0] in_c_for_div, 
    output logic [127:0] out_add,
    output logic [127:0] out_sub,
    output logic [127:0] out_negate,
    output logic [255:0] out_mul, 
    output logic [127:0] out_div,
    output logic [127:0] out_mod,
    output logic [127:0] out_pow, 
    output logic [127:0] out_and,
    output logic [127:0] out_or,
    output logic [127:0] out_xor,
    output logic [127:0] out_not,
    output logic out_red_or,
    output logic out_red_and,
    output logic out_red_xor
);
    always_comb begin
        out_add = in_a + in_b; 
        out_sub = in_a - in_b; 
        out_negate = -in_a; 
        out_mul = in_a * in_b; 
        out_div = in_a / (in_c_for_div == 128'b0 ? 128'b1 : in_c_for_div); 
        out_mod = in_a % (in_c_for_div == 128'b0 ? 128'b1 : in_c_for_div); 
        out_pow = in_a ** 2; 
        out_and = in_a & in_b; 
        out_or = in_a | in_b; 
        out_xor = in_a ^ in_b; 
        out_not = ~in_a; 
        out_red_or = |in_a; 
        out_red_and = &in_a; 
        out_red_xor = ^in_a; 
    end
endmodule
module ShiftAndCompareOps(
    input logic [31:0] in_val_u, 
    input int in_shift_amt, 
    input logic [31:0] in_comp_a_u, 
    input logic [31:0] in_comp_b_u, 
    input int in_comp_a_s, 
    input int in_comp_b_s, 
    output logic [31:0] out_shift_l,
    output logic [31:0] out_shift_r,
    output logic [31:0] out_ashift_r,
    output logic out_eq,
    output logic out_neq,
    output logic out_gt_u,
    output logic out_gte_u,
    output logic out_lt_u,
    output logic out_lte_u,
    output logic out_gt_s,
    output logic out_gte_s,
    output logic out_lt_s,
    output logic out_lte_s,
    output logic out_case_eq,
    output logic out_case_neq,
    output logic out_wild_eq,
    output logic out_wild_neq
);
    logic [31:0] signed_in_val;
    assign signed_in_val = in_val_u; 
    always_comb begin
        out_shift_l = in_val_u << in_shift_amt; 
        out_shift_r = in_val_u >> in_shift_amt; 
        out_ashift_r = signed_in_val >>> in_shift_amt; 
        out_eq = (in_comp_a_u == in_comp_b_u); 
        out_neq = (in_comp_a_u != in_comp_b_u); 
        out_gt_u = (in_comp_a_u > in_comp_b_u); 
        out_gte_u = (in_comp_a_u >= in_comp_b_u); 
        out_lt_u = (in_comp_a_u < in_comp_b_u); 
        out_lte_u = (in_comp_a_u <= in_comp_b_u); 
        out_gt_s = (in_comp_a_s > in_comp_b_s); 
        out_gte_s = (in_comp_a_s >= in_comp_b_s); 
        out_lt_s = (in_comp_a_s < in_comp_b_s); 
        out_lte_s = (in_comp_a_s <= in_comp_b_s); 
        out_case_eq = (in_comp_a_u === 32'h0000_123x); 
        out_case_neq = (in_comp_a_u !== 32'h0000_456z); 
        out_wild_eq = (in_comp_a_u[7:0] ==? 8'b1010_1XX0); 
        out_wild_neq = (in_comp_b_u[7:0] !=? 8'b0101_0ZZ0); 
    end
endmodule
module StringOps(
    input string in_str_a,
    input string in_str_b,
    input int in_index,
    input byte in_char,
    input int in_start_idx,
    input int in_end_idx,
    output int out_len,
    output string out_concat,
    output string out_repl,
    output string out_tolower,
    output string out_toupper,
    output logic out_eq_s,
    output logic out_neq_s,
    output logic out_gt_s,
    output logic out_gte_s,
    output logic out_lt_s,
    output logic out_lte_s,
    output byte out_getc,
    output string out_putc,
    output string out_substr,
    output int out_compare_case,
    output int out_compare_no_case
);
    string temp_str_putc; 
    always_comb begin
        out_len = in_str_a.len(); 
        out_concat = {in_str_a, in_str_b}; 
        out_repl = {3{in_str_a}}; 
        out_tolower = in_str_a.tolower(); 
        out_toupper = in_str_a.toupper(); 
        out_eq_s = (in_str_a == in_str_b); 
        out_neq_s = (in_str_a != in_str_b); 
        out_gt_s = (in_str_a > in_str_b); 
        out_gte_s = (in_str_a >= in_str_b); 
        out_lt_s = (in_str_a < in_str_b); 
        out_lte_s = (in_str_a <= in_str_b); 
        out_getc = in_str_a.getc(in_index); 
        temp_str_putc = in_str_a;
        temp_str_putc.putc(in_index, in_char); 
        out_putc = temp_str_putc;
        out_substr = in_str_a.substr(in_start_idx, in_end_idx); 
        out_compare_case = in_str_a.compare(in_str_b); 
        out_compare_no_case = in_str_a.compare(in_str_b, 1); 
    end
endmodule
module ConcatReplSelect(
    input logic [7:0] in_part_a,
    input logic [7:0] in_part_b,
    input logic [31:0] in_wide_val, 
    input int in_select_lsb,
    input int in_select_msb,
    input logic [7:0] in_assign_val,
    output logic [15:0] out_concat_res,
    output logic [31:0] out_repl_res,
    output logic [7:0] out_part_select_range,
    output logic [7:0] out_part_select_plus,
    output logic [7:0] out_part_select_minus,
    output logic [31:0] out_val_after_assign_into, 
    output logic [7:0] out_set_range_xz, 
    output logic [31:0] out_clean_val 
);
    logic [31:0] assign_target_val;
    logic [7:0] set_range_target;
    logic [31:0] clean_target_val;
    always_comb begin
        out_concat_res = {in_part_a, in_part_b}; 
        out_repl_res = {4{in_part_a}}; 
        out_part_select_range = in_wide_val[in_select_msb : in_select_lsb];
        out_part_select_plus = in_wide_val[in_select_lsb +: 8];
        out_part_select_minus = in_wide_val[in_select_msb -: 8];
        assign_target_val = 32'hdeadbeef;
        assign_target_val[7:0] = in_assign_val; 
        out_val_after_assign_into = assign_target_val;
        set_range_target = 8'hXX; 
        out_set_range_xz = set_range_target;
        clean_target_val = 32'hFFFF_FFFF;
        out_clean_val = clean_target_val[31:0]; 
    end
endmodule
module FourStateAndConversionOps(
    input logic [31:0] in_four_state_a,
    input logic [31:0] in_four_state_b,
    input logic [63:0] in_int_for_log2, 
    input logic [7:0] in_extend_val, 
    output logic out_is_four_state_a,
    output logic out_is_any_x_a,
    output logic out_is_any_z_a,
    output logic out_is_all_x_a,
    output logic out_is_all_z_a,
    output logic out_is_eq_zero_a,
    output logic out_is_neq_zero_a,
    output logic out_is_eq_one_a,
    output logic out_is_eq_all_ones_a,
    output logic out_is_lt_xz,
    output logic [31:0] out_bits_non_x_sim, 
    output logic [31:0] out_bits_one_sim,
    output logic [31:0] out_bits_xz_sim,
    output logic [31:0] out_bits_z_sim,
    output logic out_is_unknown,
    output logic out_one_hot,
    output logic out_one_hot0,
    output logic [5:0] out_clog2, 
    output logic [31:0] out_extend_s,
    output logic [31:0] out_extend_xz
);
    logic signed [7:0] signed_extend_val = in_extend_val; 
    logic [31:0] temp_extend_xz;
    always_comb begin
        out_is_four_state_a = in_four_state_a.is_four_state(); 
        out_is_any_x_a = in_four_state_a.is_any_x(); 
        out_is_any_z_a = in_four_state_a.is_any_z(); 
        out_is_all_x_a = in_four_state_a.is_all_x(); 
        out_is_all_z_a = in_four_state_a.is_all_z(); 
        out_is_eq_zero_a = (in_four_state_a == 32'b0); 
        out_is_neq_zero_a = (in_four_state_a != 32'b0); 
        out_is_eq_one_a = (in_four_state_a == 32'b1); 
        out_is_eq_all_ones_a = (in_four_state_a == '1); 
        out_is_lt_xz = (in_four_state_a < in_four_state_b); 
        out_bits_non_x_sim = ~(in_four_state_a ^ in_four_state_a); 
        out_bits_one_sim = in_four_state_a & 32'hFFFF_FFFF;
        out_bits_xz_sim = in_four_state_a | ~in_four_state_a; 
        out_bits_z_sim = in_four_state_a & 32'h0000_0000; 
        out_is_unknown = $isunknown(in_four_state_a); 
        out_one_hot = $onehot(in_four_state_a); 
        out_one_hot0 = $onehot0(in_four_state_a); 
        out_clog2 = $clog2(in_int_for_log2); 
        out_extend_s = signed_extend_val; 
        temp_extend_xz = in_extend_val; 
        out_extend_xz = temp_extend_xz; 
    end
endmodule
module RealNumberOps(
    input real in_real_a,
    input real in_real_b,
    input logic [63:0] in_bits_for_real, 
    input int in_int_for_real_conv_u, 
    input int in_int_for_real_conv_s, 
    output real out_neg_d,
    output real out_add_d,
    output real out_sub_d,
    output real out_mul_d,
    output real out_div_d,
    output real out_pow_d,
    output logic out_eq_d,
    output logic out_neq_d,
    output logic out_gt_d,
    output logic out_gte_d,
    output logic out_lt_d,
    output logic out_lte_d,
    output real out_real_from_bits,
    output logic [63:0] out_bits_from_real,
    output real out_real_from_uint,
    output real out_real_from_sint,
    output int out_int_from_real_s,
    output int out_int_from_real_round_s
);
    always_comb begin
        out_neg_d = -in_real_a; 
        out_add_d = in_real_a + in_real_b; 
        out_sub_d = in_real_a - in_real_b; 
        out_mul_d = in_real_a * in_real_b; 
        out_div_d = in_real_a / (in_real_b == 0.0 ? 1.0 : in_real_b); 
        out_pow_d = in_real_a ** in_real_b; 
        out_eq_d = (in_real_a == in_real_b); 
        out_neq_d = (in_real_a != in_real_b); 
        out_gt_d = (in_real_a > in_real_b); 
        out_gte_d = (in_real_a >= in_real_b); 
        out_lt_d = (in_real_a < in_real_b); 
        out_lte_d = (in_real_a <= in_real_b); 
        out_real_from_bits = $bitstoreal(in_bits_for_real); 
        out_bits_from_real = $realtobits(in_real_a); 
        out_real_from_uint = in_int_for_real_conv_u; 
        out_real_from_sint = in_int_for_real_conv_s; 
        out_int_from_real_s = int'(in_real_a); 
        out_int_from_real_round_s = $signed($floor(in_real_a + 0.5)); 
    end
endmodule
module SpecializedUtilsAndErrors(
    input logic [7:0] in_logic_a,
    input logic [7:0] in_logic_b,
    input logic [7:0] in_logic_c,
    input string in_str_val_for_aton,
    input logic [7:0] in_ens_val,
    input logic [7:0] in_if1s_val,
    output logic out_log_and,
    output logic out_log_or,
    output logic out_log_if_true,
    output logic out_log_if_false,
    output logic out_log_eq,
    output int out_ascii_to_int_dec,
    output int out_ascii_to_int_hex,
    output logic [7:0] out_bufif1_res
);
    logic [0:0] log_in_a;
    logic [0:0] log_in_b;
    logic [0:0] log_in_c;
    always_comb begin
        log_in_a = in_logic_a[0];
        log_in_b = in_logic_b[0];
        log_in_c = in_logic_c[0]; 
        out_log_and = log_in_a && log_in_b; 
        out_log_or = log_in_a || log_in_b; 
        out_log_if_true = (log_in_a ? log_in_b : log_in_c); 
        out_log_if_false = (log_in_a ? log_in_b : log_in_c); 
        out_log_eq = (log_in_a == log_in_b); 
        out_ascii_to_int_dec = in_str_val_for_aton.atoi(); 
        out_ascii_to_int_hex = in_str_val_for_aton.atohex(); 
        out_bufif1_res = in_ens_val ? in_if1s_val : 8'bZZZZZZZZ; 
    end
endmodule
