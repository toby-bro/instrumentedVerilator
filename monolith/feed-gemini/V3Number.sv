module NumLiteralsAndAssign (
    input logic [31:0] in_int,
    input logic [0:0] in_char_code_bit,
    input logic [31:0] in_unsigned_assign,
    output logic [31:0] out_dec,
    output logic [7:0] out_bin,
    output logic [15:0] out_hex,
    output logic [3:0] out_special_lit,
    output logic [63:0] out_assign_long,
    output logic [31:0] out_initial_val,
    output logic out_is_one,
    output logic out_is_all_ones,
    output logic out_is_zero,
    output logic out_is_all_x,
    output logic out_is_all_z,
    output logic [7:0] out_set_single_bits_val
);
    always_comb begin
        out_dec = 12345;
        out_bin = 8'b1010_1010;
        out_hex = 16'hABCD;
        out_special_lit = 4'b1X0Z;
        out_initial_val = 32'd0;
        out_is_one = (32'd1 == 32'd1);
        out_is_all_ones = (32'hFFFF_FFFF == 32'hFFFF_FFFF);
        out_is_zero = (32'd0 == 32'd0);
        out_is_all_x = (32'hx == 32'hx);
        out_is_all_z = (32'hz == 32'hz);
        out_set_single_bits_val = {7'b0, in_char_code_bit};
        out_assign_long = in_unsigned_assign;
        out_special_lit = in_int[3:0];
    end
endmodule
module BitwiseLogicOps (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic [7:0] out_not,
    output logic [7:0] out_and,
    output logic [7:0] out_or,
    output logic [7:0] out_xor,
    output logic out_red_or,
    output logic out_red_and,
    output logic out_red_xor,
    output logic out_log_not,
    output logic out_log_and,
    output logic out_log_or,
    output logic out_log_if,
    output logic out_log_eq
);
    always_comb begin
        out_not = ~in_a;
        out_and = in_a & in_b;
        out_or = in_a | in_b;
        out_xor = in_a ^ in_b;
        out_red_or = |in_a;
        out_red_and = &in_a;
        out_red_xor = ^in_a;
        out_log_not = !in_a;
        out_log_and = (in_a != 0) && (in_b != 0);
        out_log_or = (in_a != 0) || (in_b != 0);
        out_log_if = (in_a != 0) -> (in_b != 0);
        out_log_eq = (in_a != 0) == (in_b != 0);
    end
endmodule
module ArithmeticOpsWide (
    input logic [127:0] in_wide_a,
    input logic [127:0] in_wide_b,
    input logic signed [31:0] in_signed_a,
    input logic signed [31:0] in_signed_b,
    input logic [7:0] in_exponent_u,
    input logic signed [7:0] in_exponent_s,
    output logic [127:0] out_add,
    output logic [127:0] out_sub,
    output logic [127:0] out_mul,
    output logic [127:0] out_div,
    output logic [127:0] out_mod,
    output logic [127:0] out_negate,
    output logic signed [31:0] out_mul_s,
    output logic signed [31:0] out_div_s,
    output logic signed [31:0] out_mod_s,
    output logic [31:0] out_pow_uu,
    output logic signed [31:0] out_pow_su,
    output logic signed [31:0] out_pow_ss,
    output logic [31:0] out_pow_us
);
    always_comb begin
        out_add = in_wide_a + in_wide_b;
        out_sub = in_wide_a - in_wide_b;
        out_mul = in_wide_a * in_wide_b;
        if (in_wide_b == 0) begin
            out_div = 128'hx;
            out_mod = 128'hx;
        end else begin
            out_div = in_wide_a / in_wide_b;
            out_mod = in_wide_a % in_wide_b;
        end
        out_negate = -in_wide_a;
        if (in_signed_b == 0) begin
            out_mul_s = 32'shX;
            out_div_s = 32'shX;
            out_mod_s = 32'shX;
        end else begin
            out_mul_s = in_signed_a * in_signed_b;
            out_div_s = in_signed_a / in_signed_b;
            out_mod_s = in_signed_a % in_signed_b;
        end
        out_pow_uu = in_wide_a[31:0] ** in_exponent_u;
        out_pow_su = $signed(in_signed_a) ** in_exponent_u;
        out_pow_ss = in_signed_a ** in_exponent_s;
        out_pow_us = in_wide_a[31:0] ** in_exponent_s;
    end
endmodule
module ShiftAndSelect (
    input logic [31:0] in_data,
    input logic [4:0] in_shift_amt,
    input logic signed [31:0] in_signed_data,
    input logic [4:0] in_msb_idx,
    input logic [4:0] in_lsb_idx,
    input logic [7:0] in_buf_en,
    input logic [7:0] in_buf_data,
    output logic [31:0] out_shift_l,
    output logic [31:0] out_shift_r,
    output logic [31:0] out_shift_rs,
    output logic [31:0] out_part_select,
    output logic [7:0] out_part_select_plus,
    output logic [7:0] out_buf_if1,
    output logic [31:0] out_set_range_data_op,
    output logic [31:0] out_set_mask_op
);
    always_comb begin
        automatic logic [31:0] temp_val_for_set_range_op;
        out_shift_l = in_data << in_shift_amt;
        out_shift_r = in_data >> in_shift_amt;
        out_shift_rs = in_signed_data >>> in_shift_amt;
        out_part_select = in_data[in_lsb_idx +: (in_msb_idx - in_lsb_idx + 1)];
        out_part_select_plus = in_data[in_lsb_idx +: 8];
        out_buf_if1 = in_buf_en ? in_buf_data : 8'hz;
        temp_val_for_set_range_op = 32'hAAAA_AAAA;
        temp_val_for_set_range_op[15:8] = 8'hFF;
        temp_val_for_set_range_op[23:16] = 8'h00;
        temp_val_for_set_range_op[31:24] = 8'hXX;
        out_set_range_data_op = temp_val_for_set_range_op;
        out_set_mask_op = (32'h1 << (in_shift_amt % 32)) - 1;
    end
endmodule
module StringOpsAndConversions (
    input string in_str_base,
    input string in_str_compare,
    input int in_idx_getput,
    input int in_len_sub_len,
    input int in_char_to_put,
    input int in_repl_count,
    output int out_len_str,
    output string out_concat_str,
    output string out_repl_str,
    output string out_tolower_str,
    output string out_toupper_str,
    output int out_compare_str,
    output int out_icompare_str,
    output logic out_eq_str,
    output logic out_neq_str,
    output logic out_gt_str,
    output logic out_gte_str,
    output logic out_lt_str,
    output logic out_lte_str,
    output logic [63:0] out_atoi_dec,
    output logic [63:0] out_atoi_hex,
    output logic [63:0] out_atoi_bin,
    output int out_getc_char,
    output string out_putc_str,
    output string out_substr_str,
    output logic [31:0] out_nto_i
);
    string temp_atoi_hex = "32'hF00D";
    string temp_atoi_bin = "16'b1010_1111";
    string empty_str = "";
    always_comb begin
        automatic string temp_putc_str;
        automatic logic [255:0] temp_packed_str_for_n_to_i;
        out_len_str = in_str_base.len();
        out_concat_str = {in_str_base, in_str_compare};
        out_repl_str = {in_repl_count{in_str_base}};
        out_tolower_str = in_str_base.tolower();
        out_toupper_str = in_str_base.toupper();
        out_compare_str = in_str_base.compare(in_str_compare);
        out_icompare_str = in_str_base.icompare(in_str_compare);
        out_eq_str = (in_str_base == in_str_compare);
        out_neq_str = (in_str_base != in_str_compare);
        out_gt_str = (in_str_base > in_str_compare);
        out_gte_str = (in_str_base >= in_str_compare);
        out_lt_str = (in_str_base < in_str_compare);
        out_lte_str = (in_str_base <= in_str_compare);
        out_atoi_dec = int'(in_str_base);
        out_atoi_hex = int'(temp_atoi_hex);
        out_atoi_bin = int'(temp_atoi_bin);
        out_getc_char = in_str_base.getc(in_idx_getput);
        temp_putc_str = in_str_base;
        if (in_idx_getput >= 0 && in_idx_getput < temp_putc_str.len() && in_char_to_put != 0) begin
            temp_putc_str.putc(in_idx_getput, in_char_to_put);
        }
        out_putc_str = temp_putc_str;
        if (in_idx_getput >= 0 && in_len_sub_len > 0 && (in_idx_getput + in_len_sub_len - 1) < in_str_base.len()) begin
            out_substr_str = in_str_base.substr(in_idx_getput, in_idx_getput + in_len_sub_len - 1);
        } else begin
            out_substr_str = empty_str;
        end
        temp_packed_str_for_n_to_i = 0;
        for (int i = 0; i < in_str_base.len(); i++) begin
            if (i*8 + 7 < 256) begin
                temp_packed_str_for_n_to_i[i*8 +: 8] = in_str_base.getc(in_str_base.len() - 1 - i);
            end
        end
        out_nto_i = temp_packed_str_for_n_to_i[31:0];
    end
endmodule
module RealNumberOps (
    input real in_real_val_a,
    input real in_real_val_b,
    input logic [63:0] in_real_bits_in,
    input logic [31:0] in_logic_for_itor,
    input logic signed [31:0] in_signed_for_itor,
    output real out_real_neg,
    output real out_real_sum,
    output real out_real_diff,
    output real out_real_prod,
    output real out_real_quot,
    output real out_real_pow,
    output logic out_real_eq,
    output logic out_real_neq,
    output logic out_real_gt,
    output logic out_real_gte,
    output logic out_real_lt,
    output logic out_real_lte,
    output logic [63:0] out_real_to_bits_conv,
    output real out_bits_to_real_conv,
    output int out_rtoi_s,
    output int out_round_s,
    output real out_itor_u,
    output real out_itor_s
);
    always_comb begin
        out_real_neg = -in_real_val_a;
        out_real_sum = in_real_val_a + in_real_val_b;
        out_real_diff = in_real_val_a - in_real_val_b;
        out_real_prod = in_real_val_a * in_real_val_b;
        out_real_quot = in_real_val_a / (in_real_val_b == 0.0 ? 1.0 : in_real_val_b);
        out_real_pow = in_real_val_a ** in_real_val_b;
        out_real_eq = (in_real_val_a == in_real_val_b);
        out_real_neq = (in_real_val_a != in_real_val_b);
        out_real_gt = (in_real_val_a > in_real_val_b);
        out_real_gte = (in_real_val_a >= in_real_val_b);
        out_real_lt = (in_real_val_a < in_real_val_b);
        out_real_lte = (in_real_val_a <= in_real_val_b);
        out_real_to_bits_conv = in_real_val_a;
        out_bits_to_real_conv = in_real_bits_in;
        out_rtoi_s = $rtoi(in_real_val_a);
        out_round_s = $rtoi(in_real_val_a + 0.5);
        out_itor_u = $itor(in_logic_for_itor);
        out_itor_s = $itor(in_signed_for_itor);
    end
endmodule
module NumPropsAndBits (
    input logic [31:0] in_val_prop,
    input logic [31:0] in_val_x_z,
    output int out_to_uint,
    output int out_to_sint,
    output longint out_to_uquad,
    output longint out_to_squad,
    output int out_count_ones,
    output int out_count_bits_1,
    output int out_count_bits_x,
    output int out_count_bits_z,
    output logic out_is_all_x_check,
    output logic out_is_all_z_check,
    output logic out_is_eq_zero_check,
    output logic out_is_neq_zero_check,
    output logic out_is_eq_one_check,
    output logic out_is_eq_all_ones_check,
    output logic out_is_bits_zero_check,
    output logic out_is_lt_xz_val,
    output int out_clog2,
    output logic out_onehot,
    output logic out_onehot0,
    output logic out_isunknown,
    output logic out_wild_eq,
    output logic out_wild_neq
);
    always_comb begin
        out_to_uint = in_val_prop;
        out_to_sint = $signed(in_val_prop);
        out_to_uquad = in_val_prop;
        out_to_squad = $signed(in_val_prop);
        out_count_ones = $countones(in_val_prop);
        out_count_bits_1 = $countbits(in_val_x_z, 1'b1);
        out_count_bits_x = $countbits(in_val_x_z, 1'bx);
        out_count_bits_z = $countbits(in_val_x_z, 1'bz);
        out_is_all_x_check = (in_val_x_z === 32'hx);
        out_is_all_z_check = (in_val_x_z === 32'hz);
        out_is_eq_zero_check = (in_val_prop == 0);
        out_is_neq_zero_check = (in_val_prop != 0);
        out_is_eq_one_check = (in_val_prop == 1);
        out_is_eq_all_ones_check = (in_val_prop == 32'hFFFF_FFFF);
        out_is_bits_zero_check = (in_val_prop[7:0] == 0);
        out_is_lt_xz_val = (32'b101x < 32'b1010);
        out_clog2 = $clog2(in_val_prop == 0 ? 1 : in_val_prop);
        out_onehot = $onehot(in_val_prop);
        out_onehot0 = $onehot0(in_val_prop);
        out_isunknown = $isunknown(in_val_x_z);
        out_wild_eq = (in_val_x_z ==? 32'b101x);
        out_wild_neq = (in_val_x_z !=? 32'b010z);
    end
endmodule
module StreamAndCast (
    input logic [63:0] in_packed_data,
    input int in_stream_size_in,
    input logic [7:0] in_small_val_s,
    input logic [7:0] in_small_val_xz,
    output logic [63:0] out_stream_left,
    output logic signed [63:0] out_signed_extend,
    output logic [63:0] out_xz_extend,
    output logic [31:0] out_clean_op
);
    parameter int STREAM_SIZE = 8;
    always_comb begin
        out_stream_left = {>>STREAM_SIZE{in_packed_data}};
        out_signed_extend = $signed(in_small_val_s);
        case (in_small_val_xz[7])
            1'bx: out_xz_extend = 64'hx;
            1'bz: out_xz_extend = 64'hz;
            default: out_xz_extend = in_small_val_xz;
        endcase
        out_clean_op = in_packed_data[31:0];
    end
endmodule
