module Comb_IfElse (
    input wire condition,
    input wire [15:0] value1,
    input wire [15:0] value2,
    output reg [15:0] result_val
);
    always_comb begin
        if (condition) begin
            result_val = value1;
        end else begin
            result_val = value2;
        end
    end
endmodule

module LintSensitiveList (
    input logic in_p,
    input logic in_q,
    output logic out_r
);
    always_comb begin
        out_r = in_p | in_q;
    end
endmodule

module ansi_directions (
    input logic control_in,
    input logic data_ref_in,
    output logic data_ref_out,
    output logic status_out,
    inout wire data_inout
);
    logic internal_data = 1'b0;
    assign data_inout = internal_data;
    always_comb begin
        data_ref_out = data_ref_in;
        internal_data = data_inout;
        status_out = internal_data | control_in;
    end
endmodule

module m_driver_check (
    input bit clk,
    input int val_in,
    output int driven_var
);
    int my_driven_var;
    function automatic void write_to_var(input int val);
        my_driven_var = val;
    endfunction
    always @(posedge clk) begin
        write_to_var(val_in);
    end
    assign driven_var = my_driven_var;
endmodule

module module_forceable_attr (
    input wire i_clk,
    input logic i_data_in,
    input wire i_rst_n,
    input logic i_write_en,
    output logic o_forceable_signal,
    output logic o_read_signal
);
    logic forceable_signal ;
    logic read_internal;
    assign o_forceable_signal = forceable_signal;
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            forceable_signal <= 1'b0;
            read_internal <= 1'b0;
        end else begin
            if (i_write_en) begin
                forceable_signal <= i_data_in;
            end
            read_internal <= forceable_signal;
        end
    end
    assign o_read_signal = read_internal;
endmodule

module unpacked_array_module (
    input wire [7:0] in_array_data,
    input wire [1:0] select_idx,
    output wire [3:0] out_element
);
    logic [3:0] data_array [4];
    always @(*) begin
        data_array[0] = in_array_data[3:0];
        data_array[1] = in_array_data[7:4];
        data_array[2] = 4'd8;
        data_array[3] = 4'd12;
    end
    assign out_element = data_array[select_idx];
endmodule

module snippet (
    input wire clk,
    input wire [15:0] inj_i_packed_data_1755007812756_368,
    input wire [7:0] inj_in_array_data_1755007812751_840,
    input integer inj_in_int_1755007812741_656,
    input logic [31:0] inj_in_l32_1755007812741_300,
    input logic inj_in_p_1755007812744_520,
    input logic inj_in_q_1755007812745_33,
    input logic signed [7:0] inj_in_s8_1755007812741_852,
    input logic [15:0] inj_in_u16_1755007812741_358,
    input logic [3:0] inj_input_bf_slice_1755007812741_738,
    input logic [2:0] inj_mode_1755007812742_210,
    input wire [1:0] inj_select_idx_1755007812751_819,
    input int inj_val_in_1755007812740_927,
    input wire [15:0] inj_value1_1755007812778_532,
    input wire reset,
    output logic [7:0] inj_concat_out_1755007812749_220,
    output logic inj_data_ref_out_1755007812748_263,
    output logic [15:0] inj_dcac_end_val_1755007812762_769,
    output int inj_driven_var_1755007812740_749,
    output logic inj_o_forceable_signal_1755007812753_74,
    output logic [7:0] inj_o_member_sum_1755007812756_133,
    output logic inj_o_read_signal_1755007812753_435,
    output logic [7:0] inj_o_target_result_1755007812783_470,
    output wire [3:0] inj_out_element_1755007812751_151,
    output logic inj_out_r_1755007812745_363,
    output logic [7:0] inj_out_reg_d_1755007812774_466,
    output logic signed [15:0] inj_out_s16_1755007812741_194,
    output logic signed [31:0] inj_out_s32_from_int_1755007812741_13,
    output logic signed [31:0] inj_out_s32_from_l32_1755007812741_740,
    output logic [31:0] inj_out_u32_from_int_1755007812741_8,
    output logic [31:0] inj_out_u32_from_l32_1755007812741_681,
    output logic [7:0] inj_out_u8_1755007812741_836,
    output int inj_out_val_1755007812746_610,
    output int inj_out_val_1755007812760_711,
    output logic [7:0] inj_output_bf_1755007812741_728,
    output logic [3:0] inj_output_bf_slice_1755007812741_646,
    output logic [7:0] inj_res_1755007812742_651,
    output reg [15:0] inj_result_val_1755007812778_810,
    output logic inj_status_out_1755007812748_441,
    inout wire inj_data_inout_1755007812748_414
);
    // BEGIN: SignedUnsignedConversions_ts1755007812741
    // BEGIN: module_bitfield_concat_ts1755007812742
    logic [7:0] my_bitfield_ts1755007812742 ;
        // BEGIN: macro_concat_user_ts1755007812749
        `define MAKE_NAME(a,b) a``b
        logic var_signal_ts1755007812749;
            // BEGIN: deep_comb_assign_chain_ts1755007812770
            logic [15:0] t1_ts1755007812763, t2_ts1755007812763, t3_ts1755007812763, t4_ts1755007812763, t5_ts1755007812763, t6_ts1755007812763, t7_ts1755007812763, t8_ts1755007812763, t9_ts1755007812763, t10_ts1755007812763;
            logic [15:0] t11_ts1755007812763, t12_ts1755007812763, t13_ts1755007812763, t14_ts1755007812763, t15_ts1755007812763, t16_ts1755007812763, t17_ts1755007812763, t18_ts1755007812763, t19_ts1755007812763, t20_ts1755007812763;
            logic [15:0] t21_ts1755007812763, t22_ts1755007812763, t23_ts1755007812763, t24_ts1755007812763, t25_ts1755007812763, t26_ts1755007812763, t27_ts1755007812763, t28_ts1755007812763, t29_ts1755007812763, t30_ts1755007812763;
            logic [15:0] t31_ts1755007812763, t32_ts1755007812763, t33_ts1755007812763, t34_ts1755007812763, t35_ts1755007812763, t36_ts1755007812763, t37_ts1755007812763, t38_ts1755007812763, t39_ts1755007812763, t40_ts1755007812763;
                // BEGIN: target_module_for_bind_ts1755007812783
                always_comb inj_o_target_result_1755007812783_470 = inj_in_s8_1755007812741_852 + 1;
                // END: target_module_for_bind_ts1755007812783

                Comb_IfElse Comb_IfElse_inst_1755007812778_1726 (
                    .value2(inj_i_packed_data_1755007812756_368),
                    .result_val(inj_result_val_1755007812778_810),
                    .condition(clk),
                    .value1(inj_value1_1755007812778_532)
                );
                // BEGIN: split_conditional_nb_ts1755007812774
                always @(posedge clk) begin
                    if (var_signal_ts1755007812749) begin
                        inj_out_reg_d_1755007812774_466 <= inj_in_s8_1755007812741_852;
                    end else begin
                        inj_out_reg_d_1755007812774_466 <= my_bitfield_ts1755007812742;
                    end
                end
                // END: split_conditional_nb_ts1755007812774

            always_comb begin
                t1_ts1755007812763 = inj_i_packed_data_1755007812756_368 + 1;
                t2_ts1755007812763 = t1_ts1755007812763 * 2;
                t3_ts1755007812763 = t2_ts1755007812763 - 3;
                t4_ts1755007812763 = t3_ts1755007812763 ^ 4;
                t5_ts1755007812763 = t4_ts1755007812763 | 5;
                t6_ts1755007812763 = t5_ts1755007812763 & 6;
                t7_ts1755007812763 = t6_ts1755007812763 + 7;
                t8_ts1755007812763 = t7_ts1755007812763 - 8;
                t9_ts1755007812763 = t8_ts1755007812763 ^ 9;
                t10_ts1755007812763 = t9_ts1755007812763 | 10;
                t11_ts1755007812763 = t10_ts1755007812763 & 11;
                t12_ts1755007812763 = t11_ts1755007812763 + 12;
                t13_ts1755007812763 = t12_ts1755007812763 - 13;
                t14_ts1755007812763 = t13_ts1755007812763 ^ 14;
                t15_ts1755007812763 = t14_ts1755007812763 | 15;
                t16_ts1755007812763 = t15_ts1755007812763 + 16;
                t17_ts1755007812763 = t16_ts1755007812763 * 17;
                t18_ts1755007812763 = t17_ts1755007812763 - 18;
                t19_ts1755007812763 = t18_ts1755007812763 ^ 19;
                t20_ts1755007812763 = t19_ts1755007812763 | 20;
                t21_ts1755007812763 = t20_ts1755007812763 + 1;
                t22_ts1755007812763 = t21_ts1755007812763 * 2;
                t23_ts1755007812763 = t22_ts1755007812763 - 3;
                t24_ts1755007812763 = t23_ts1755007812763 ^ 4;
                t25_ts1755007812763 = t24_ts1755007812763 | 5;
                t26_ts1755007812763 = t25_ts1755007812763 & 6;
                t27_ts1755007812763 = t26_ts1755007812763 + 7;
                t28_ts1755007812763 = t27_ts1755007812763 - 8;
                t29_ts1755007812763 = t28_ts1755007812763 ^ 9;
                t30_ts1755007812763 = t29_ts1755007812763 | 10;
                t31_ts1755007812763 = t30_ts1755007812763 & 11;
                t32_ts1755007812763 = t31_ts1755007812763 + 12;
                t33_ts1755007812763 = t32_ts1755007812763 - 13;
                t34_ts1755007812763 = t33_ts1755007812763 ^ 14;
                t35_ts1755007812763 = t34_ts1755007812763 | 15;
                t36_ts1755007812763 = t35_ts1755007812763 + 16;
                t37_ts1755007812763 = t36_ts1755007812763 * 17;
                t38_ts1755007812763 = t37_ts1755007812763 - 18;
                t39_ts1755007812763 = t38_ts1755007812763 ^ 19;
                t40_ts1755007812763 = t39_ts1755007812763 | 20;
                inj_dcac_end_val_1755007812762_769 = t40_ts1755007812763;
            end
            // END: deep_comb_assign_chain_ts1755007812770

            // BEGIN: undeclared_but_found_pkg_diag_mod_ts1755007812760
            assign inj_out_val_1755007812760_711 = inj_val_in_1755007812740_927;
            // END: undeclared_but_found_pkg_diag_mod_ts1755007812760

            // BEGIN: module_struct_ts1755007812756
            typedef struct packed {
                logic [3:0] part1_ts1755007812756;
                logic [7:0] part2_ts1755007812756;
                logic [3:0] part3_ts1755007812756;
            } my_packed_struct_t;
            my_packed_struct_t unpacked_data;
            assign unpacked_data = inj_i_packed_data_1755007812756_368;
            always @* begin
                inj_o_member_sum_1755007812756_133 = unpacked_data.part1_ts1755007812756 + unpacked_data.part2_ts1755007812756 + unpacked_data.part3_ts1755007812756;
            end
            // END: module_struct_ts1755007812756

            module_forceable_attr module_forceable_attr_inst_1755007812753_926 (
                .i_data_in(var_signal_ts1755007812749),
                .i_rst_n(reset),
                .i_write_en(inj_in_q_1755007812745_33),
                .o_forceable_signal(inj_o_forceable_signal_1755007812753_74),
                .o_read_signal(inj_o_read_signal_1755007812753_435),
                .i_clk(clk)
            );
            unpacked_array_module unpacked_array_module_inst_1755007812751_146 (
                .in_array_data(inj_in_array_data_1755007812751_840),
                .select_idx(inj_select_idx_1755007812751_819),
                .out_element(inj_out_element_1755007812751_151)
            );
        always_comb begin
            `MAKE_NAME(var,_signal) = inj_input_bf_slice_1755007812741_738[0];
        end
        assign inj_concat_out_1755007812749_220 = {4'b0, inj_input_bf_slice_1755007812741_738[3:1], var_signal_ts1755007812749};
        // END: macro_concat_user_ts1755007812749

        ansi_directions ansi_directions_inst_1755007812748_9571 (
            .data_ref_in(inj_in_q_1755007812745_33),
            .data_ref_out(inj_data_ref_out_1755007812748_263),
            .status_out(inj_status_out_1755007812748_441),
            .data_inout(inj_data_inout_1755007812748_414),
            .control_in(inj_in_p_1755007812744_520)
        );
        // BEGIN: undeclared_but_found_pkg_diag_mod_ts1755007812746
        assign inj_out_val_1755007812746_610 = inj_val_in_1755007812740_927;
        // END: undeclared_but_found_pkg_diag_mod_ts1755007812746

        LintSensitiveList LintSensitiveList_inst_1755007812745_9115 (
            .in_q(inj_in_q_1755007812745_33),
            .out_r(inj_out_r_1755007812745_363),
            .in_p(inj_in_p_1755007812744_520)
        );
        // BEGIN: dup_nested_if_ts1755007812743
        always_comb begin
            inj_res_1755007812742_651 = '0;
            if (inj_mode_1755007812742_210 == 3'b001) begin
                if (inj_in_s8_1755007812741_852 > my_bitfield_ts1755007812742) begin
                    inj_res_1755007812742_651 = inj_in_s8_1755007812741_852 + my_bitfield_ts1755007812742;
                end else begin
                    inj_res_1755007812742_651 = inj_in_s8_1755007812741_852 - my_bitfield_ts1755007812742;
                end
            end else if (inj_mode_1755007812742_210 == 3'b010) begin
                if (inj_in_s8_1755007812741_852 > my_bitfield_ts1755007812742) begin
                    inj_res_1755007812742_651 = inj_in_s8_1755007812741_852 + my_bitfield_ts1755007812742;
                end else begin
                    inj_res_1755007812742_651 = inj_in_s8_1755007812741_852 - my_bitfield_ts1755007812742;
                end
            end else if (inj_mode_1755007812742_210 == 3'b011) begin
                if (inj_in_s8_1755007812741_852 < my_bitfield_ts1755007812742) begin
                    inj_res_1755007812742_651 = inj_in_s8_1755007812741_852 * my_bitfield_ts1755007812742;
                end else begin
                    inj_res_1755007812742_651 = inj_in_s8_1755007812741_852 / ((my_bitfield_ts1755007812742 == 0) ? 1 : my_bitfield_ts1755007812742);
                end
            end else if (inj_mode_1755007812742_210 == 3'b100) begin
                if (inj_in_s8_1755007812741_852 != my_bitfield_ts1755007812742) begin
                    if (inj_in_s8_1755007812741_852 > my_bitfield_ts1755007812742) inj_res_1755007812742_651 = inj_in_s8_1755007812741_852;
                    else inj_res_1755007812742_651 = my_bitfield_ts1755007812742;
                end else begin
                    inj_res_1755007812742_651 = inj_in_s8_1755007812741_852 + my_bitfield_ts1755007812742;
                end
            end
            else begin
                inj_res_1755007812742_651 = inj_in_s8_1755007812741_852 ^ my_bitfield_ts1755007812742;
            end
        end
        // END: dup_nested_if_ts1755007812743

    always_comb begin
        if (inj_in_s8_1755007812741_852[7]) begin
            my_bitfield_ts1755007812742 = inj_in_s8_1755007812741_852;
        end else begin
            my_bitfield_ts1755007812742 = {inj_in_s8_1755007812741_852[0], inj_in_s8_1755007812741_852[7:1]};
        end
        my_bitfield_ts1755007812742[3:0] = inj_input_bf_slice_1755007812741_738;
    end
    assign inj_output_bf_1755007812741_728 = my_bitfield_ts1755007812742;
    assign inj_output_bf_slice_1755007812741_646 = my_bitfield_ts1755007812742[3:0];
    // END: module_bitfield_concat_ts1755007812742

    always_comb begin
        inj_out_u8_1755007812741_836 = $unsigned(inj_in_s8_1755007812741_852);
        inj_out_s16_1755007812741_194 = $signed(inj_in_u16_1755007812741_358);
        inj_out_s32_from_l32_1755007812741_740 = $signed(inj_in_l32_1755007812741_300);
        inj_out_u32_from_l32_1755007812741_681 = $unsigned(inj_in_l32_1755007812741_300);
        inj_out_s32_from_int_1755007812741_13 = $signed(inj_in_int_1755007812741_656);
        inj_out_u32_from_int_1755007812741_8 = $unsigned(inj_in_int_1755007812741_656);
    end
    // END: SignedUnsignedConversions_ts1755007812741

    m_driver_check m_driver_check_inst_1755007812740_8747 (
        .clk(clk),
        .val_in(inj_val_in_1755007812740_927),
        .driven_var(inj_driven_var_1755007812740_749)
    );
endmodule

