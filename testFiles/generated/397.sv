module Comb_Assign (
    input wire in1,
    input wire in2,
    output wire out
);
    assign out = in1 & in2;
endmodule

module always_comb_assign (
    input logic [15:0] in,
    output logic [15:0] out
);
    always_comb begin
        out = in;
    end
endmodule

module ansi_implicit_inherit (
    input logic [2:0] in1,
    input logic in2,
    output logic extra_out,
    output logic out1,
    output logic out2
);
    always_comb begin
        out1 = |in1;
        out2 = |in2;
        extra_out = out1 ^ out2;
    end
endmodule

module mod_default_disable (
    input bit enable_in,
    output bit out
);
    assign out = enable_in;
endmodule

module net_var_conn_child (
    input logic in_logic,
    output logic out_wire
);
    assign out_wire = in_logic;
endmodule

module udnt_port_module (
    input logic udnt_input,
    input logic uin,
    output logic udnt_output,
    output logic uout
);
    assign uout = uin;
    assign udnt_output = udnt_input;
endmodule

module snippet (
    input wire clk,
    input bit [7:0] inj_data_in_1755007887274_246,
    input logic [2:0] inj_in1_1755007887287_213,
    input logic [7:0] inj_in1_f_1755007887275_655,
    input logic [31:0] inj_in2_1755007887304_922,
    input logic [15:0] inj_in2_1755007887308_497,
    input logic [7:0] inj_in2_f_1755007887275_284,
    input logic [15:0] inj_in3_1755007887308_287,
    input logic [7:0] inj_in3_f_1755007887275_3,
    input logic [15:0] inj_in4_1755007887308_916,
    input logic [15:0] inj_in5_1755007887308_24,
    input wire [7:0] inj_in_a_1755007887296_139,
    input wire [7:0] inj_in_b_1755007887296_427,
    input wire [7:0] inj_in_c_1755007887296_967,
    input wire [7:0] inj_in_const1_1755007887296_24,
    input wire [7:0] inj_in_const2_1755007887296_612,
    input logic [3:0] inj_in_h_1755007887280_379,
    input logic [3:0] inj_in_l_1755007887280_866,
    input logic inj_in_logic_1755007887274_919,
    input logic [1:0] inj_in_val_1755007887288_138,
    input logic [31:0] inj_nested_in_1755007887302_194,
    input logic [15:0] inj_packed_in_1755007887273_461,
    input bit inj_select_signal_1755007887274_92,
    input logic inj_uin_1755007887274_736,
    input logic [63:0] inj_wide_a_1755007887295_951,
    input logic [63:0] inj_wide_b_1755007887294_473,
    input logic [63:0] inj_wide_c_1755007887294_688,
    input wire reset,
    output logic inj_bind_out_1755007887281_448,
    output bit inj_cfg_out_1755007887291_151,
    output bit [7:0] inj_data_out_1755007887274_892,
    output logic inj_extra_out_1755007887287_215,
    output logic [7:0] inj_field2_o_1755007887273_411,
    output logic [7:0] inj_inner_field_o_1755007887302_917,
    output logic inj_named_out_1755007887276_484,
    output logic inj_o_done_1755007887290_775,
    output logic inj_out1_1755007887284_511,
    output logic inj_out1_1755007887287_870,
    output logic [7:0] inj_out1_a_1755007887276_190,
    output logic [7:0] inj_out1_f_1755007887275_809,
    output logic inj_out2_1755007887284_119,
    output logic inj_out2_1755007887287_239,
    output logic [7:0] inj_out2_f_1755007887275_171,
    output logic [7:0] inj_out3_f_1755007887275_858,
    output logic [15:0] inj_out_1755007887277_957,
    output logic inj_out_1755007887278_194,
    output bit inj_out_1755007887278_702,
    output wire inj_out_1755007887282_19,
    output logic [31:0] inj_out_1755007887304_513,
    output logic inj_out_1755007887308_316,
    output logic [7:0] inj_out_add_assoc_1755007887296_996,
    output logic [7:0] inj_out_and_assoc_1755007887296_361,
    output logic [7:0] inj_out_and_swap_const_1755007887296_140,
    output logic [7:0] inj_out_arith_1755007887296_833,
    output logic [7:0] inj_out_bitwise_1755007887296_574,
    output logic [7:0] inj_out_c_1755007887280_164,
    output logic inj_out_logical_1755007887296_532,
    output logic [7:0] inj_out_mul_assoc_1755007887296_332,
    output logic [7:0] inj_out_negate_1755007887296_983,
    output logic [7:0] inj_out_or_assoc_1755007887296_300,
    output logic [7:0] inj_out_or_swap_not_1755007887296_34,
    output logic [7:0] inj_out_p_g_1755007887306_138,
    output logic [7:0] inj_out_q_g_1755007887306_5,
    output reg inj_out_res_1755007887288_470,
    output logic [7:0] inj_out_unary_not_1755007887296_512,
    output logic [8:0] inj_out_val_c_l_1755007887285_304,
    output logic [7:0] inj_out_val_d_l_1755007887285_379,
    output logic [7:0] inj_out_val_m10_1755007887283_67,
    output logic [7:0] inj_out_vec_y_1755007887293_239,
    output logic inj_out_wire_1755007887274_194,
    output logic [7:0] inj_out_xor_assoc_1755007887296_163,
    output logic [7:0] inj_out_xor_swap_var_1755007887296_795,
    output logic inj_reset_n_1755007887279_276,
    output logic inj_udnt_output_1755007887274_526,
    output logic inj_uout_1755007887274_997,
    output logic [63:0] inj_wide_out_1755007887294_797
);
    // BEGIN: typedef_struct_mod_ts1755007887273
    typedef struct packed {
        logic [7:0] field1_ts1755007887273;
        logic [7:0] field2_ts1755007887273;
    } my_packed_struct_t;
    my_packed_struct_t my_struct_var;
    // BEGIN: SimpleLogicTest_ts1755007887274
    logic [7:0] temp_data_ts1755007887274;
    // BEGIN: module_with_param_ts1755007887276
    parameter int DELAY = 10;
    logic bind_dummy_in_ts1755007887276;
    logic bind_dummy_out_ts1755007887276;
    // BEGIN: unsupported_cond_expr_ts1755007887283
    logic [7:0] var_m10_ts1755007887283;
    // BEGIN: module_unpacked_array_ts1755007887284
    logic [1:0] data_ua[0:1] ;
    // BEGIN: mod_basic_ts1755007887290
    logic r_state_ts1755007887290;
    parameter int PARAM_BASIC = 42;
    // BEGIN: Mod_BasicOps_ts1755007887300
    logic [7:0] intermediate_arith_ts1755007887299;
    logic [7:0] intermediate_bitwise_ts1755007887299;
    logic [0:0] intermediate_logical_ts1755007887299;
    logic [7:0] intermediate_add_assoc_ts1755007887299;
    logic [7:0] intermediate_mul_assoc_ts1755007887299;
    logic [7:0] intermediate_and_assoc_ts1755007887299;
    logic [7:0] intermediate_or_assoc_ts1755007887299;
    logic [7:0] intermediate_xor_assoc_ts1755007887299;
    parameter [7:0] CONST_ZERO = 8'h00;
    // BEGIN: nested_types_mod_ts1755007887302
    typedef struct packed {
        logic [7:0] inner_field_ts1755007887302;
        logic [7:0] padding_ts1755007887302;
    } inner_struct_t;
    typedef union packed {
        logic [31:0] full_word_ts1755007887302;
        struct packed {
            logic [15:0] unused_ts1755007887302;
            inner_struct_t inner_data;
        } outer_fields;
    } outer_union_t;
    outer_union_t nested_var;
    // BEGIN: split_reorder_blocking_ts1755007887306
    logic [7:0] mid_x_g_ts1755007887306;
    logic [7:0] mid_y_g_ts1755007887306;
    // BEGIN: arith_comp_ops_ts1755007887308
    assign inj_out_1755007887308_316 = (inj_packed_in_1755007887273_461 + inj_in2_1755007887308_497) * inj_in3_1755007887308_287 > inj_in4_1755007887308_916 - inj_in5_1755007887308_24;
    // END: arith_comp_ops_ts1755007887308

    always @(*) begin
        mid_x_g_ts1755007887306 = inj_in3_f_1755007887275_3 * 2;
        mid_y_g_ts1755007887306 = mid_x_g_ts1755007887306 + inj_in2_f_1755007887275_284;
        inj_out_p_g_1755007887306_138 = mid_y_g_ts1755007887306 - 1;
        inj_out_q_g_1755007887306_5 = mid_x_g_ts1755007887306 / 2;
    end
    // END: split_reorder_blocking_ts1755007887306

    // BEGIN: always_comb_if_ts1755007887304
    always_comb begin
        if (inj_uin_1755007887274_736) begin
            inj_out_1755007887304_513 = inj_nested_in_1755007887302_194;
        end else begin
            inj_out_1755007887304_513 = inj_in2_1755007887304_922;
        end
    end
    // END: always_comb_if_ts1755007887304

    always_comb begin
        nested_var.full_word_ts1755007887302 = inj_nested_in_1755007887302_194;
    end
    assign inj_inner_field_o_1755007887302_917 = nested_var.outer_fields.inner_data.inner_field_ts1755007887302;
    // END: nested_types_mod_ts1755007887302

    always_comb begin
        intermediate_arith_ts1755007887299 = inj_in_a_1755007887296_139;
        intermediate_arith_ts1755007887299 = intermediate_arith_ts1755007887299 + inj_in_b_1755007887296_427;
        intermediate_arith_ts1755007887299 = intermediate_arith_ts1755007887299 - inj_in_c_1755007887296_967;
        intermediate_arith_ts1755007887299 = intermediate_arith_ts1755007887299 * inj_in_const1_1755007887296_24;
        if (inj_in_b_1755007887296_427 != CONST_ZERO) begin
            intermediate_arith_ts1755007887299 = intermediate_arith_ts1755007887299 / inj_in_b_1755007887296_427;
            intermediate_arith_ts1755007887299 = intermediate_arith_ts1755007887299 % inj_in_b_1755007887296_427;
        end else begin
            intermediate_arith_ts1755007887299 = 'x;
        end
        inj_out_arith_1755007887296_833 = intermediate_arith_ts1755007887299;
        intermediate_bitwise_ts1755007887299 = inj_in_a_1755007887296_139;
        intermediate_bitwise_ts1755007887299 = intermediate_bitwise_ts1755007887299 & inj_in_b_1755007887296_427;
        intermediate_bitwise_ts1755007887299 = intermediate_bitwise_ts1755007887299 | inj_in_c_1755007887296_967;
        intermediate_bitwise_ts1755007887299 = intermediate_bitwise_ts1755007887299 ^ inj_in_const1_1755007887296_24;
        inj_out_bitwise_1755007887296_574 = intermediate_bitwise_ts1755007887299;
        intermediate_logical_ts1755007887299 = (inj_in_a_1755007887296_139 != CONST_ZERO) && (inj_in_b_1755007887296_427 != CONST_ZERO);
        intermediate_logical_ts1755007887299 = intermediate_logical_ts1755007887299 || (inj_in_c_1755007887296_967 != CONST_ZERO);
        inj_out_logical_1755007887296_532 = !intermediate_logical_ts1755007887299;
        inj_out_unary_not_1755007887296_512 = ~inj_in_a_1755007887296_139;
        inj_out_negate_1755007887296_983 = -inj_in_a_1755007887296_139;
        intermediate_add_assoc_ts1755007887299 = (inj_in_a_1755007887296_139 + inj_in_b_1755007887296_427) + inj_in_c_1755007887296_967;
        inj_out_add_assoc_1755007887296_996 = intermediate_add_assoc_ts1755007887299;
        intermediate_mul_assoc_ts1755007887299 = (inj_in_a_1755007887296_139 * inj_in_b_1755007887296_427) * inj_in_c_1755007887296_967;
        inj_out_mul_assoc_1755007887296_332 = intermediate_mul_assoc_ts1755007887299;
        intermediate_and_assoc_ts1755007887299 = (inj_in_a_1755007887296_139 & inj_in_b_1755007887296_427) & inj_in_c_1755007887296_967;
        inj_out_and_assoc_1755007887296_361 = intermediate_and_assoc_ts1755007887299;
        intermediate_or_assoc_ts1755007887299 = (inj_in_a_1755007887296_139 | inj_in_b_1755007887296_427) | inj_in_c_1755007887296_967;
        inj_out_or_assoc_1755007887296_300 = intermediate_or_assoc_ts1755007887299;
        intermediate_xor_assoc_ts1755007887299 = (inj_in_a_1755007887296_139 ^ inj_in_b_1755007887296_427) ^ inj_in_c_1755007887296_967;
        inj_out_xor_assoc_1755007887296_163 = intermediate_xor_assoc_ts1755007887299;
        inj_out_and_swap_const_1755007887296_140 = inj_in_const1_1755007887296_24 & inj_in_a_1755007887296_139;
        inj_out_or_swap_not_1755007887296_34 = (~inj_in_a_1755007887296_139) | inj_in_b_1755007887296_427;
        inj_out_xor_swap_var_1755007887296_795 = inj_in_b_1755007887296_427 ^ inj_in_c_1755007887296_967;
    end
    // END: Mod_BasicOps_ts1755007887300

    // BEGIN: wide_ops_deep_ts1755007887295
    assign inj_wide_out_1755007887294_797 = (((inj_wide_a_1755007887295_951 + inj_wide_b_1755007887294_473) ^ inj_wide_c_1755007887294_688) & (~inj_wide_a_1755007887295_951 | inj_wide_b_1755007887294_473)) + (inj_wide_c_1755007887294_688 >>> 5);
    // END: wide_ops_deep_ts1755007887295

    // BEGIN: split_vector_assign_ts1755007887293
    always @(posedge clk) begin
        if (inj_in_logic_1755007887274_919) begin
            inj_out_vec_y_1755007887293_239[3:0] <= inj_in1_f_1755007887275_655[3:0];
            inj_out_vec_y_1755007887293_239[7:4] <= inj_in1_f_1755007887275_655[7:4] + 1;
        end else begin
            inj_out_vec_y_1755007887293_239 <= 8'hFF;
        end
    end
    // END: split_vector_assign_ts1755007887293

    // BEGIN: Module_ConfigKeywords_ts1755007887291
    assign inj_cfg_out_1755007887291_151 = inj_select_signal_1755007887274_92;
    // END: Module_ConfigKeywords_ts1755007887291

    always_ff @(posedge clk) begin
        r_state_ts1755007887290 <= ~r_state_ts1755007887290;
    end
    always_comb begin
        inj_o_done_1755007887290_775 = r_state_ts1755007887290;
    end
    // END: mod_basic_ts1755007887290

    // BEGIN: case_default_ts1755007887288
    always_comb begin
        inj_out_res_1755007887288_470 = 1'b0;
        case (inj_in_val_1755007887288_138)
            2'b01: inj_out_res_1755007887288_470 = 1'b1;
            2'b10: inj_out_res_1755007887288_470 = 1'b0;
            default: inj_out_res_1755007887288_470 = 1'b1;
        endcase
    end
    // END: case_default_ts1755007887288

    ansi_implicit_inherit ansi_implicit_inherit_inst_1755007887287_9326 (
        .in1(inj_in1_1755007887287_213),
        .in2(inj_uin_1755007887274_736),
        .extra_out(inj_extra_out_1755007887287_215),
        .out1(inj_out1_1755007887287_870),
        .out2(inj_out2_1755007887287_239)
    );
    // BEGIN: split_inputs_outputs_only_ts1755007887286
    always @(*) begin
        inj_out_val_c_l_1755007887285_304 = inj_in2_f_1755007887275_284 + inj_in3_f_1755007887275_3;
        inj_out_val_d_l_1755007887285_379 = inj_in2_f_1755007887275_284 - inj_in3_f_1755007887275_3;
    end
    // END: split_inputs_outputs_only_ts1755007887286

    always_comb begin
        data_ua[0][0] = inj_uin_1755007887274_736;
        data_ua[0][1] = inj_in_logic_1755007887274_919;
        data_ua[1][0] = data_ua[0][0];
        data_ua[1][1] = ~data_ua[0][1];
    end
    assign inj_out1_1755007887284_511 = data_ua[1][0];
    assign inj_out2_1755007887284_119 = data_ua[1][1];
    // END: module_unpacked_array_ts1755007887284

    always_comb begin
        var_m10_ts1755007887283 = inj_in3_f_1755007887275_3;
        inj_out_val_m10_1755007887283_67 = inj_select_signal_1755007887274_92 ? var_m10_ts1755007887283 : var_m10_ts1755007887283;
        var_m10_ts1755007887283++;
    end
    // END: unsupported_cond_expr_ts1755007887283

    Comb_Assign Comb_Assign_inst_1755007887282_2399 (
        .in2(reset),
        .out(inj_out_1755007887282_19),
        .in1(clk)
    );
    // BEGIN: bind_module_ts1755007887281
    assign inj_bind_out_1755007887281_448 = inj_in_logic_1755007887274_919;
    // END: bind_module_ts1755007887281

    // BEGIN: concat_op_ts1755007887280
    assign inj_out_c_1755007887280_164 = {inj_in_h_1755007887280_379, inj_in_l_1755007887280_866};
    // END: concat_op_ts1755007887280

    // BEGIN: ansi_basic_ts1755007887279
    always_comb begin
        inj_reset_n_1755007887279_276 = clk;
    end
    // END: ansi_basic_ts1755007887279

    // BEGIN: reduction_ops_ts1755007887279
    assign inj_out_1755007887278_194 = &inj_in2_f_1755007887275_284 | ^inj_in3_f_1755007887275_3;
    // END: reduction_ops_ts1755007887279

    mod_default_disable mod_default_disable_inst_1755007887278_4527 (
        .enable_in(inj_select_signal_1755007887274_92),
        .out(inj_out_1755007887278_702)
    );
    always_comb_assign always_comb_assign_inst_1755007887277_6207 (
        .in(inj_packed_in_1755007887273_461),
        .out(inj_out_1755007887277_957)
    );
    // BEGIN: split_basic_blocking_ts1755007887276
    always @(*) begin
        inj_out1_a_1755007887276_190 = inj_in2_f_1755007887275_284;
    end
    // END: split_basic_blocking_ts1755007887276

    assign inj_named_out_1755007887276_484 = inj_in_logic_1755007887274_919;
    // END: module_with_param_ts1755007887276

    // BEGIN: split_independent_nb_ts1755007887275
    always @(posedge clk) begin
        inj_out1_f_1755007887275_809 <= inj_in1_f_1755007887275_655;
        inj_out2_f_1755007887275_171 <= inj_in2_f_1755007887275_284;
        inj_out3_f_1755007887275_858 <= inj_in3_f_1755007887275_3;
    end
    // END: split_independent_nb_ts1755007887275

    udnt_port_module udnt_port_module_inst_1755007887274_4125 (
        .uin(inj_uin_1755007887274_736),
        .udnt_output(inj_udnt_output_1755007887274_526),
        .uout(inj_uout_1755007887274_997),
        .udnt_input(inj_in_logic_1755007887274_919)
    );
    always_comb begin
        if (inj_select_signal_1755007887274_92) begin
            temp_data_ts1755007887274 = inj_data_in_1755007887274_246 + 1;
        end else begin
            temp_data_ts1755007887274 = inj_data_in_1755007887274_246 - 1;
        end
        inj_data_out_1755007887274_892 = temp_data_ts1755007887274;
    end
    // END: SimpleLogicTest_ts1755007887274

    net_var_conn_child net_var_conn_child_inst_1755007887274_8812 (
        .in_logic(inj_in_logic_1755007887274_919),
        .out_wire(inj_out_wire_1755007887274_194)
    );
    always_comb begin
        my_struct_var = inj_packed_in_1755007887273_461;
    end
    assign inj_field2_o_1755007887273_411 = my_struct_var.field2_ts1755007887273;
    // END: typedef_struct_mod_ts1755007887273
endmodule

