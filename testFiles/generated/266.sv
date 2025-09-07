interface struct_if;
    logic [7:0] packet_field1;
    logic [7:0] packet_field2;
    logic tx_en;
    modport Access (output packet_field1, output packet_field2, output tx_en);
endinterface
module concat_assign (
    input logic [7:0] in,
    output logic [3:0] out_h,
    output logic [3:0] out_l
);
    assign {out_h, out_l} = in;
endmodule

module mod_internal_if_test (
    input wire in_i,
    output logic out_o
);
    assign out_o = !in_i;
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_a_1755007843417_844,
    input logic [3:0] inj_b_1755007843417_813,
    input logic inj_b_1755007843440_696,
    input logic inj_d_1755007843405_819,
    input bit [7:0] inj_data1_1755007843402_66,
    input bit [7:0] inj_data2_1755007843402_850,
    input wire [15:0] inj_dcac_start_val_1755007843419_718,
    input int inj_diag_input_val_1755007843403_18,
    input logic [15:0] inj_in_1755007843404_737,
    input wire [7:0] inj_in_a_1755007843406_633,
    input wire [7:0] inj_in_b_1755007843406_802,
    input wire [7:0] inj_in_c_1755007843406_500,
    input wire [7:0] inj_in_const1_1755007843406_696,
    input wire [7:0] inj_in_const2_1755007843406_315,
    input logic [7:0] inj_in_field1_1755007843403_495,
    input logic [7:0] inj_in_field2_1755007843403_581,
    input logic [1:0] inj_in_val_1755007843415_641,
    input bit inj_sel_1755007843402_947,
    input wire [1:0] inj_select_idx_1755007843445_566,
    input wire reset,
    output logic [3:0] inj_data_out_1755007843434_246,
    output logic [15:0] inj_dcac_end_val_1755007843419_678,
    output bit inj_diag_output_flag_1755007843403_348,
    output logic [7:0] inj_diff_v_1755007843450_710,
    output logic [15:0] inj_out_1755007843404_545,
    output logic [7:0] inj_out_add_assoc_1755007843406_897,
    output logic [7:0] inj_out_and_assoc_1755007843406_236,
    output logic [7:0] inj_out_and_swap_const_1755007843406_865,
    output logic [7:0] inj_out_arith_1755007843406_996,
    output logic [7:0] inj_out_bitwise_1755007843406_496,
    output wire [3:0] inj_out_element_1755007843445_992,
    output logic [3:0] inj_out_h_1755007843430_644,
    output logic [3:0] inj_out_l_1755007843430_565,
    output logic inj_out_logical_1755007843406_782,
    output logic [7:0] inj_out_mul_assoc_1755007843406_101,
    output logic [7:0] inj_out_negate_1755007843406_314,
    output logic inj_out_o_1755007843403_319,
    output logic [7:0] inj_out_or_assoc_1755007843406_140,
    output logic [7:0] inj_out_or_swap_not_1755007843406_317,
    output reg inj_out_res_1755007843415_274,
    output logic [7:0] inj_out_unary_not_1755007843406_935,
    output logic [7:0] inj_out_xor_assoc_1755007843406_398,
    output logic [7:0] inj_out_xor_swap_var_1755007843406_47,
    output logic [7:0] inj_prod_v_1755007843450_30,
    output logic inj_q_1755007843405_92,
    output bit [7:0] inj_result1_1755007843402_889,
    output bit [7:0] inj_result2_1755007843402_96,
    output logic [3:0] inj_sum_1755007843417_463,
    output logic inj_sum_1755007843439_2,
    output logic [7:0] inj_sum_v_1755007843450_562,
    output logic inj_tx_status_1755007843403_845
);
    // BEGIN: comb_conditional_ts1755007843402
    // BEGIN: module_struct_write_ts1755007843403
    // BEGIN: PragmaDiagnosticDirective_ts1755007843404
`ifdef SLANG_PRAGMA
`diagnostic push
`endif
`ifdef SLANG_PRAGMA
`diagnostic ignore "SLANG_UNUSED_VARIABLE"
`endif
`ifdef SLANG_PRAGMA
`diagnostic warn "SLANG_IMPLICIT_CAST"
`endif
`ifdef SLANG_PRAGMA
`diagnostic error "SLANG_MULTIPLE_DRIVER"
`endif
`ifdef SLANG_PRAGMA
`diagnostic fatal "SLANG_SYNTAX_ERROR_FATAL"
`endif
`ifdef SLANG_PRAGMA
    // BEGIN: always_comb_assign_ts1755007843404
    // BEGIN: ModClockedResetReg_ts1755007843405
    // BEGIN: Mod_BasicOps_ts1755007843413
    logic [7:0] intermediate_arith_ts1755007843410;
    logic [7:0] intermediate_bitwise_ts1755007843410;
    logic [0:0] intermediate_logical_ts1755007843410;
    logic [7:0] intermediate_add_assoc_ts1755007843410;
    logic [7:0] intermediate_mul_assoc_ts1755007843410;
    logic [7:0] intermediate_and_assoc_ts1755007843410;
    logic [7:0] intermediate_or_assoc_ts1755007843410;
    logic [7:0] intermediate_xor_assoc_ts1755007843410;
        // BEGIN: deep_comb_assign_chain_ts1755007843427
        logic [15:0] t1_ts1755007843420, t2_ts1755007843420, t3_ts1755007843420, t4_ts1755007843420, t5_ts1755007843420, t6_ts1755007843420, t7_ts1755007843420, t8_ts1755007843420, t9_ts1755007843420, t10_ts1755007843420;
        logic [15:0] t11_ts1755007843420, t12_ts1755007843420, t13_ts1755007843420, t14_ts1755007843420, t15_ts1755007843420, t16_ts1755007843420, t17_ts1755007843420, t18_ts1755007843420, t19_ts1755007843420, t20_ts1755007843420;
        logic [15:0] t21_ts1755007843420, t22_ts1755007843420, t23_ts1755007843420, t24_ts1755007843420, t25_ts1755007843420, t26_ts1755007843420, t27_ts1755007843420, t28_ts1755007843420, t29_ts1755007843420, t30_ts1755007843420;
        logic [15:0] t31_ts1755007843420, t32_ts1755007843420, t33_ts1755007843420, t34_ts1755007843420, t35_ts1755007843420, t36_ts1755007843420, t37_ts1755007843420, t38_ts1755007843420, t39_ts1755007843420, t40_ts1755007843420;
            // BEGIN: sequential_logic_ts1755007843434
            ;
            logic [3:0] internal_reg_ts1755007843434;
                // BEGIN: unpacked_array_module_ts1755007843445
                logic [3:0] data_array_ts1755007843445 [4];
                    // BEGIN: split_arith_nb_ts1755007843450
                    always @(posedge clk) begin
                        inj_sum_v_1755007843450_562 <= intermediate_mul_assoc_ts1755007843410 + intermediate_arith_ts1755007843410;
                        inj_diff_v_1755007843450_710 <= intermediate_mul_assoc_ts1755007843410 - intermediate_arith_ts1755007843410;
                        inj_prod_v_1755007843450_30 <= intermediate_mul_assoc_ts1755007843410 * intermediate_arith_ts1755007843410;
                    end
                    // END: split_arith_nb_ts1755007843450

                always @(*) begin
                    data_array_ts1755007843445[0] = inj_in_a_1755007843406_633[3:0];
                    data_array_ts1755007843445[1] = inj_in_a_1755007843406_633[7:4];
                    data_array_ts1755007843445[2] = 4'd8;
                    data_array_ts1755007843445[3] = 4'd12;
                end
                assign inj_out_element_1755007843445_992 = data_array_ts1755007843445[inj_select_idx_1755007843445_566];
                // END: unpacked_array_module_ts1755007843445

                // BEGIN: simple_adder_ts1755007843440
                assign inj_sum_1755007843439_2 = inj_d_1755007843405_819 + inj_b_1755007843440_696;
                // END: simple_adder_ts1755007843440

            always_ff @(posedge clk or negedge reset) begin
                if (!reset) begin
                    internal_reg_ts1755007843434 <= 4'h0;
                end else begin
                    internal_reg_ts1755007843434 <= inj_b_1755007843417_813;
                end
            end
            assign inj_data_out_1755007843434_246 = internal_reg_ts1755007843434;
            // END: sequential_logic_ts1755007843434

            concat_assign concat_assign_inst_1755007843430_7844 (
                .out_l(inj_out_l_1755007843430_565),
                .in(intermediate_mul_assoc_ts1755007843410),
                .out_h(inj_out_h_1755007843430_644)
            );
        always_comb begin
            t1_ts1755007843420 = inj_dcac_start_val_1755007843419_718 + 1;
            t2_ts1755007843420 = t1_ts1755007843420 * 2;
            t3_ts1755007843420 = t2_ts1755007843420 - 3;
            t4_ts1755007843420 = t3_ts1755007843420 ^ 4;
            t5_ts1755007843420 = t4_ts1755007843420 | 5;
            t6_ts1755007843420 = t5_ts1755007843420 & 6;
            t7_ts1755007843420 = t6_ts1755007843420 + 7;
            t8_ts1755007843420 = t7_ts1755007843420 - 8;
            t9_ts1755007843420 = t8_ts1755007843420 ^ 9;
            t10_ts1755007843420 = t9_ts1755007843420 | 10;
            t11_ts1755007843420 = t10_ts1755007843420 & 11;
            t12_ts1755007843420 = t11_ts1755007843420 + 12;
            t13_ts1755007843420 = t12_ts1755007843420 - 13;
            t14_ts1755007843420 = t13_ts1755007843420 ^ 14;
            t15_ts1755007843420 = t14_ts1755007843420 | 15;
            t16_ts1755007843420 = t15_ts1755007843420 + 16;
            t17_ts1755007843420 = t16_ts1755007843420 * 17;
            t18_ts1755007843420 = t17_ts1755007843420 - 18;
            t19_ts1755007843420 = t18_ts1755007843420 ^ 19;
            t20_ts1755007843420 = t19_ts1755007843420 | 20;
            t21_ts1755007843420 = t20_ts1755007843420 + 1;
            t22_ts1755007843420 = t21_ts1755007843420 * 2;
            t23_ts1755007843420 = t22_ts1755007843420 - 3;
            t24_ts1755007843420 = t23_ts1755007843420 ^ 4;
            t25_ts1755007843420 = t24_ts1755007843420 | 5;
            t26_ts1755007843420 = t25_ts1755007843420 & 6;
            t27_ts1755007843420 = t26_ts1755007843420 + 7;
            t28_ts1755007843420 = t27_ts1755007843420 - 8;
            t29_ts1755007843420 = t28_ts1755007843420 ^ 9;
            t30_ts1755007843420 = t29_ts1755007843420 | 10;
            t31_ts1755007843420 = t30_ts1755007843420 & 11;
            t32_ts1755007843420 = t31_ts1755007843420 + 12;
            t33_ts1755007843420 = t32_ts1755007843420 - 13;
            t34_ts1755007843420 = t33_ts1755007843420 ^ 14;
            t35_ts1755007843420 = t34_ts1755007843420 | 15;
            t36_ts1755007843420 = t35_ts1755007843420 + 16;
            t37_ts1755007843420 = t36_ts1755007843420 * 17;
            t38_ts1755007843420 = t37_ts1755007843420 - 18;
            t39_ts1755007843420 = t38_ts1755007843420 ^ 19;
            t40_ts1755007843420 = t39_ts1755007843420 | 20;
            inj_dcac_end_val_1755007843419_678 = t40_ts1755007843420;
        end
        // END: deep_comb_assign_chain_ts1755007843427

        // BEGIN: CombinationalLogicImplicit_ts1755007843417
        always @* begin
            inj_sum_1755007843417_463 = inj_a_1755007843417_844 + inj_b_1755007843417_813;
        end
        // END: CombinationalLogicImplicit_ts1755007843417

        // BEGIN: case_basic_ts1755007843415
        always_comb begin
            inj_out_res_1755007843415_274 = 1'b0;
            case (inj_in_val_1755007843415_641)
                2'b00: inj_out_res_1755007843415_274 = 1'b0;
                2'b01: inj_out_res_1755007843415_274 = 1'b1;
                2'b10: inj_out_res_1755007843415_274 = 1'b0;
                2'b11: inj_out_res_1755007843415_274 = 1'b1;
            endcase
        end
        // END: case_basic_ts1755007843415

    parameter [7:0] CONST_ZERO = 8'h00;
    always_comb begin
        intermediate_arith_ts1755007843410 = inj_in_a_1755007843406_633;
        intermediate_arith_ts1755007843410 = intermediate_arith_ts1755007843410 + inj_in_b_1755007843406_802;
        intermediate_arith_ts1755007843410 = intermediate_arith_ts1755007843410 - inj_in_c_1755007843406_500;
        intermediate_arith_ts1755007843410 = intermediate_arith_ts1755007843410 * inj_in_const1_1755007843406_696;
        if (inj_in_b_1755007843406_802 != CONST_ZERO) begin
            intermediate_arith_ts1755007843410 = intermediate_arith_ts1755007843410 / inj_in_b_1755007843406_802;
            intermediate_arith_ts1755007843410 = intermediate_arith_ts1755007843410 % inj_in_b_1755007843406_802;
        end else begin
            intermediate_arith_ts1755007843410 = 'x;
        end
        inj_out_arith_1755007843406_996 = intermediate_arith_ts1755007843410;
        intermediate_bitwise_ts1755007843410 = inj_in_a_1755007843406_633;
        intermediate_bitwise_ts1755007843410 = intermediate_bitwise_ts1755007843410 & inj_in_b_1755007843406_802;
        intermediate_bitwise_ts1755007843410 = intermediate_bitwise_ts1755007843410 | inj_in_c_1755007843406_500;
        intermediate_bitwise_ts1755007843410 = intermediate_bitwise_ts1755007843410 ^ inj_in_const1_1755007843406_696;
        inj_out_bitwise_1755007843406_496 = intermediate_bitwise_ts1755007843410;
        intermediate_logical_ts1755007843410 = (inj_in_a_1755007843406_633 != CONST_ZERO) && (inj_in_b_1755007843406_802 != CONST_ZERO);
        intermediate_logical_ts1755007843410 = intermediate_logical_ts1755007843410 || (inj_in_c_1755007843406_500 != CONST_ZERO);
        inj_out_logical_1755007843406_782 = !intermediate_logical_ts1755007843410;
        inj_out_unary_not_1755007843406_935 = ~inj_in_a_1755007843406_633;
        inj_out_negate_1755007843406_314 = -inj_in_a_1755007843406_633;
        intermediate_add_assoc_ts1755007843410 = (inj_in_a_1755007843406_633 + inj_in_b_1755007843406_802) + inj_in_c_1755007843406_500;
        inj_out_add_assoc_1755007843406_897 = intermediate_add_assoc_ts1755007843410;
        intermediate_mul_assoc_ts1755007843410 = (inj_in_a_1755007843406_633 * inj_in_b_1755007843406_802) * inj_in_c_1755007843406_500;
        inj_out_mul_assoc_1755007843406_101 = intermediate_mul_assoc_ts1755007843410;
        intermediate_and_assoc_ts1755007843410 = (inj_in_a_1755007843406_633 & inj_in_b_1755007843406_802) & inj_in_c_1755007843406_500;
        inj_out_and_assoc_1755007843406_236 = intermediate_and_assoc_ts1755007843410;
        intermediate_or_assoc_ts1755007843410 = (inj_in_a_1755007843406_633 | inj_in_b_1755007843406_802) | inj_in_c_1755007843406_500;
        inj_out_or_assoc_1755007843406_140 = intermediate_or_assoc_ts1755007843410;
        intermediate_xor_assoc_ts1755007843410 = (inj_in_a_1755007843406_633 ^ inj_in_b_1755007843406_802) ^ inj_in_c_1755007843406_500;
        inj_out_xor_assoc_1755007843406_398 = intermediate_xor_assoc_ts1755007843410;
        inj_out_and_swap_const_1755007843406_865 = inj_in_const1_1755007843406_696 & inj_in_a_1755007843406_633;
        inj_out_or_swap_not_1755007843406_317 = (~inj_in_a_1755007843406_633) | inj_in_b_1755007843406_802;
        inj_out_xor_swap_var_1755007843406_47 = inj_in_b_1755007843406_802 ^ inj_in_c_1755007843406_500;
    end
    // END: Mod_BasicOps_ts1755007843413

    always @(posedge clk or negedge reset) begin
    if (!reset) begin
        inj_q_1755007843405_92 <= 1'b0;
    end else begin
        inj_q_1755007843405_92 <= inj_d_1755007843405_819;
    end
    end
    // END: ModClockedResetReg_ts1755007843405

    always_comb begin
        inj_out_1755007843404_545 = inj_in_1755007843404_737;
    end
    // END: always_comb_assign_ts1755007843404

`diagnostic ignore (value=("SLANG_UNDRIVEN_SIGNAL", "SLANG_UNREAD_SIGNAL"))
`endif
`ifdef SLANG_PRAGMA
`diagnostic warn (value="SLANG_LATCH_INFERRED")
`endif
assign inj_diag_output_flag_1755007843403_348 = (inj_diag_input_val_1755007843403_18 > 0);
`ifdef SLANG_PRAGMA
`diagnostic pop
`endif
    // END: PragmaDiagnosticDirective_ts1755007843404

    mod_internal_if_test mod_internal_if_test_inst_1755007843403_7988 (
        .out_o(inj_out_o_1755007843403_319),
        .in_i(clk)
    );
    struct_if stif_inst();
    always_comb begin
        stif_inst.packet_field1 = inj_in_field1_1755007843403_495;
        stif_inst.packet_field2 = inj_in_field2_1755007843403_581;
        stif_inst.tx_en = 1'b1;
        inj_tx_status_1755007843403_845 = stif_inst.tx_en;
    end
    // END: module_struct_write_ts1755007843403

    always @* begin
        if (inj_sel_1755007843402_947) begin
            inj_result1_1755007843402_889 = inj_data1_1755007843402_66;
            inj_result2_1755007843402_96 = inj_data1_1755007843402_66;
        end else begin
            inj_result1_1755007843402_889 = inj_data2_1755007843402_850;
            inj_result2_1755007843402_96 = inj_data2_1755007843402_850;
        end
    end
    // END: comb_conditional_ts1755007843402
endmodule

