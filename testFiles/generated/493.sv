module ModClockedConditional (
    input logic clk,
    input logic data_in,
    input logic enable,
    output logic data_out
);
    logic reg_data;
    always @(posedge clk) begin
    if (enable) begin
        reg_data <= data_in;
    end
    end
    assign data_out = reg_data;
endmodule

module ModRegister (
    input logic din,
    output logic dout
);
    always @* begin
        dout = din;
    end
endmodule

module div_mod_ops (
    input logic [7:0] denominator,
    input logic [15:0] dividend_mod,
    input logic [7:0] divisor_mod,
    input logic [15:0] numerator,
    output logic [15:0] quotient,
    output logic [7:0] remainder
);
    assign quotient = (denominator == 0) ? 16'hFFFF : (numerator / denominator); 
    assign remainder = (divisor_mod == 0) ? 8'hFF : (dividend_mod % divisor_mod);
endmodule

module primitive_example (
    input logic i_p1,
    input logic i_p2,
    output logic o_p_and,
    output logic o_p_xor
);
    and (o_p_and, i_p1, i_p2);
    xor (o_p_xor, i_p1, i_p2);
endmodule

module sub_inst_array_mod (
    input logic [7:0] in,
    output logic [7:0] out
);
    assign out = in;
endmodule

module unsupported_cond_expr (
    input bit condition_m10,
    input logic [7:0] in_val_m10,
    output logic [7:0] out_val_m10
);
    logic [7:0] var_m10;
    always_comb begin
        var_m10 = in_val_m10;
        out_val_m10 = condition_m10 ? var_m10 : var_m10;
        var_m10++;
    end
endmodule

module snippet (
    input wire clk,
    input bit inj_condition_m10_1755007919117_185,
    input logic inj_data_in_1755007919118_910,
    input logic [15:0] inj_dividend_mod_1755007919117_355,
    input logic [7:0] inj_divisor_mod_1755007919117_313,
    input logic inj_enable_1755007919118_380,
    input logic [31:0] inj_in_1755007919117_489,
    input wire [7:0] inj_in_a_1755007919118_206,
    input wire [7:0] inj_in_b_1755007919118_189,
    input wire [7:0] inj_in_c_1755007919118_427,
    input wire [7:0] inj_in_const1_1755007919118_619,
    input wire [7:0] inj_in_const2_1755007919118_95,
    input int inj_in_val_1755007919117_62,
    input logic [7:0] inj_in_val_m10_1755007919117_651,
    input logic [15:0] inj_numerator_1755007919117_742,
    input wire reset,
    output logic inj_data_out_1755007919118_912,
    output logic inj_dout_1755007919124_217,
    output logic [7:0] inj_inner_field_o_1755007919122_684,
    output logic inj_o_p_and_1755007919125_281,
    output logic inj_o_p_and_1755007919127_610,
    output logic inj_o_p_xor_1755007919125_837,
    output logic inj_o_p_xor_1755007919127_911,
    output logic [7:0] inj_out1_1755007919117_247,
    output logic inj_out2_1755007919117_933,
    output logic [7:0] inj_out_1755007919118_828,
    output logic [7:0] inj_out_add_assoc_1755007919118_812,
    output logic [7:0] inj_out_and_assoc_1755007919118_979,
    output logic [7:0] inj_out_and_swap_const_1755007919118_758,
    output logic [7:0] inj_out_arith_1755007919118_199,
    output logic [7:0] inj_out_bitwise_1755007919118_338,
    output logic inj_out_logical_1755007919118_243,
    output logic [7:0] inj_out_mul_assoc_1755007919118_354,
    output logic [3:0] inj_out_narrow_1755007919117_171,
    output logic [7:0] inj_out_negate_1755007919118_444,
    output logic [7:0] inj_out_or_assoc_1755007919118_255,
    output logic [7:0] inj_out_or_swap_not_1755007919118_831,
    output logic [7:0] inj_out_unary_not_1755007919118_401,
    output int inj_out_val_1755007919117_857,
    output logic [7:0] inj_out_val_m10_1755007919117_324,
    output logic [7:0] inj_out_xor_assoc_1755007919118_997,
    output logic [7:0] inj_out_xor_swap_var_1755007919118_248,
    output logic [15:0] inj_quotient_1755007919117_554,
    output logic [7:0] inj_remainder_1755007919117_768,
    output logic inj_reset_n_1755007919128_579
);
    // BEGIN: constant_sel_ts1755007919117
    // BEGIN: super_outside_class_diag_mod_ts1755007919117
    // BEGIN: LintImplicitWidth_ts1755007919117
    // BEGIN: Mod_BasicOps_ts1755007919121
    logic [7:0] intermediate_arith_ts1755007919120;
    logic [7:0] intermediate_bitwise_ts1755007919120;
    logic [0:0] intermediate_logical_ts1755007919120;
    logic [7:0] intermediate_add_assoc_ts1755007919120;
    logic [7:0] intermediate_mul_assoc_ts1755007919120;
    logic [7:0] intermediate_and_assoc_ts1755007919120;
    logic [7:0] intermediate_or_assoc_ts1755007919120;
    logic [7:0] intermediate_xor_assoc_ts1755007919120;
        // BEGIN: ansi_basic_ts1755007919128
        always_comb begin
            inj_reset_n_1755007919128_579 = clk;
        end
        // END: ansi_basic_ts1755007919128

        primitive_example primitive_example_inst_1755007919127_7852 (
            .o_p_and(inj_o_p_and_1755007919127_610),
            .o_p_xor(inj_o_p_xor_1755007919127_911),
            .i_p1(inj_enable_1755007919118_380),
            .i_p2(inj_data_in_1755007919118_910)
        );
        // BEGIN: primitive_example_ts1755007919125
        and (inj_o_p_and_1755007919125_281, inj_data_in_1755007919118_910, inj_enable_1755007919118_380);
        xor (inj_o_p_xor_1755007919125_837, inj_data_in_1755007919118_910, inj_enable_1755007919118_380);
        // END: primitive_example_ts1755007919125

        ModRegister ModRegister_inst_1755007919124_3158 (
            .dout(inj_dout_1755007919124_217),
            .din(inj_enable_1755007919118_380)
        );
        // BEGIN: nested_types_mod_ts1755007919123
        typedef struct packed {
            logic [7:0] inner_field_ts1755007919123;
            logic [7:0] padding_ts1755007919123;
        } inner_struct_t;
        typedef union packed {
            logic [31:0] full_word_ts1755007919123;
            struct packed {
                logic [15:0] unused_ts1755007919123;
                inner_struct_t inner_data;
            } outer_fields;
        } outer_union_t;
        outer_union_t nested_var;
        always_comb begin
            nested_var.full_word_ts1755007919123 = inj_in_1755007919117_489;
        end
        assign inj_inner_field_o_1755007919122_684 = nested_var.outer_fields.inner_data.inner_field_ts1755007919123;
        // END: nested_types_mod_ts1755007919123

    parameter [7:0] CONST_ZERO = 8'h00;
    always_comb begin
        intermediate_arith_ts1755007919120 = inj_in_a_1755007919118_206;
        intermediate_arith_ts1755007919120 = intermediate_arith_ts1755007919120 + inj_in_b_1755007919118_189;
        intermediate_arith_ts1755007919120 = intermediate_arith_ts1755007919120 - inj_in_c_1755007919118_427;
        intermediate_arith_ts1755007919120 = intermediate_arith_ts1755007919120 * inj_in_const1_1755007919118_619;
        if (inj_in_b_1755007919118_189 != CONST_ZERO) begin
            intermediate_arith_ts1755007919120 = intermediate_arith_ts1755007919120 / inj_in_b_1755007919118_189;
            intermediate_arith_ts1755007919120 = intermediate_arith_ts1755007919120 % inj_in_b_1755007919118_189;
        end else begin
            intermediate_arith_ts1755007919120 = 'x;
        end
        inj_out_arith_1755007919118_199 = intermediate_arith_ts1755007919120;
        intermediate_bitwise_ts1755007919120 = inj_in_a_1755007919118_206;
        intermediate_bitwise_ts1755007919120 = intermediate_bitwise_ts1755007919120 & inj_in_b_1755007919118_189;
        intermediate_bitwise_ts1755007919120 = intermediate_bitwise_ts1755007919120 | inj_in_c_1755007919118_427;
        intermediate_bitwise_ts1755007919120 = intermediate_bitwise_ts1755007919120 ^ inj_in_const1_1755007919118_619;
        inj_out_bitwise_1755007919118_338 = intermediate_bitwise_ts1755007919120;
        intermediate_logical_ts1755007919120 = (inj_in_a_1755007919118_206 != CONST_ZERO) && (inj_in_b_1755007919118_189 != CONST_ZERO);
        intermediate_logical_ts1755007919120 = intermediate_logical_ts1755007919120 || (inj_in_c_1755007919118_427 != CONST_ZERO);
        inj_out_logical_1755007919118_243 = !intermediate_logical_ts1755007919120;
        inj_out_unary_not_1755007919118_401 = ~inj_in_a_1755007919118_206;
        inj_out_negate_1755007919118_444 = -inj_in_a_1755007919118_206;
        intermediate_add_assoc_ts1755007919120 = (inj_in_a_1755007919118_206 + inj_in_b_1755007919118_189) + inj_in_c_1755007919118_427;
        inj_out_add_assoc_1755007919118_812 = intermediate_add_assoc_ts1755007919120;
        intermediate_mul_assoc_ts1755007919120 = (inj_in_a_1755007919118_206 * inj_in_b_1755007919118_189) * inj_in_c_1755007919118_427;
        inj_out_mul_assoc_1755007919118_354 = intermediate_mul_assoc_ts1755007919120;
        intermediate_and_assoc_ts1755007919120 = (inj_in_a_1755007919118_206 & inj_in_b_1755007919118_189) & inj_in_c_1755007919118_427;
        inj_out_and_assoc_1755007919118_979 = intermediate_and_assoc_ts1755007919120;
        intermediate_or_assoc_ts1755007919120 = (inj_in_a_1755007919118_206 | inj_in_b_1755007919118_189) | inj_in_c_1755007919118_427;
        inj_out_or_assoc_1755007919118_255 = intermediate_or_assoc_ts1755007919120;
        intermediate_xor_assoc_ts1755007919120 = (inj_in_a_1755007919118_206 ^ inj_in_b_1755007919118_189) ^ inj_in_c_1755007919118_427;
        inj_out_xor_assoc_1755007919118_997 = intermediate_xor_assoc_ts1755007919120;
        inj_out_and_swap_const_1755007919118_758 = inj_in_const1_1755007919118_619 & inj_in_a_1755007919118_206;
        inj_out_or_swap_not_1755007919118_831 = (~inj_in_a_1755007919118_206) | inj_in_b_1755007919118_189;
        inj_out_xor_swap_var_1755007919118_248 = inj_in_b_1755007919118_189 ^ inj_in_c_1755007919118_427;
    end
    // END: Mod_BasicOps_ts1755007919121

    ModClockedConditional ModClockedConditional_inst_1755007919118_2676 (
        .data_out(inj_data_out_1755007919118_912),
        .clk(clk),
        .data_in(inj_data_in_1755007919118_910),
        .enable(inj_enable_1755007919118_380)
    );
    sub_inst_array_mod sub_inst_array_mod_inst_1755007919118_9032 (
        .out(inj_out_1755007919118_828),
        .in(inj_divisor_mod_1755007919117_313)
    );
    assign inj_out_narrow_1755007919117_171 = inj_divisor_mod_1755007919117_313;
    // END: LintImplicitWidth_ts1755007919117

    div_mod_ops div_mod_ops_inst_1755007919117_9303 (
        .remainder(inj_remainder_1755007919117_768),
        .denominator(inj_in_val_m10_1755007919117_651),
        .dividend_mod(inj_dividend_mod_1755007919117_355),
        .divisor_mod(inj_divisor_mod_1755007919117_313),
        .numerator(inj_numerator_1755007919117_742),
        .quotient(inj_quotient_1755007919117_554)
    );
    unsupported_cond_expr unsupported_cond_expr_inst_1755007919117_7847 (
        .out_val_m10(inj_out_val_m10_1755007919117_324),
        .condition_m10(inj_condition_m10_1755007919117_185),
        .in_val_m10(inj_in_val_m10_1755007919117_651)
    );
    assign inj_out_val_1755007919117_857 = inj_in_val_1755007919117_62;
    // END: super_outside_class_diag_mod_ts1755007919117

    assign inj_out1_1755007919117_247 = inj_in_1755007919117_489[15:8];
    assign inj_out2_1755007919117_933 = inj_in_1755007919117_489[3];
    // END: constant_sel_ts1755007919117
endmodule

