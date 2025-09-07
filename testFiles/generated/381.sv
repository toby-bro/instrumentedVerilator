interface cond_if;
    logic [15:0] control_reg;
    logic [15:0] status_reg;
    modport CtrlStat (output control_reg, input status_reg);
endinterface
module BindSimpleModule (
    input bit in,
    output bit out
);
    assign out = in;
endmodule

module Module_ConfigKeywords (
    input bit cfg_in,
    output bit cfg_out
);
    assign cfg_out = cfg_in;
endmodule

module SimpleLoopExample (
    input logic [7:0] in_vec,
    output logic [7:0] out_vec
);
    always_comb begin
        for (int i = 0; i < 8; i++) begin
            out_vec[i] = in_vec[7 - i];
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_data_in_1755007882062_441,
    input wire [15:0] inj_dcac_start_val_1755007882064_305,
    input logic inj_dummy_in_1755007882063_689,
    input wire [3:0] inj_in0_1755007882063_31,
    input wire [3:0] inj_in1_1755007882063_351,
    input wire [3:0] inj_in2_1755007882063_346,
    input wire [3:0] inj_in3_1755007882063_982,
    input logic [7:0] inj_in_b_1755007882071_771,
    input bit inj_in_tc_1755007882087_611,
    input logic [1:0] inj_in_val_1755007882062_216,
    input int inj_in_val_1755007882062_762,
    input logic [2:0] inj_in_val_1755007882084_769,
    input wire [1:0] inj_sel_1755007882063_44,
    input wire reset,
    output logic inj_control_status_1755007882105_250,
    output logic [7:0] inj_data_out_1755007882062_208,
    output logic [15:0] inj_dcac_end_val_1755007882064_990,
    output logic inj_dummy_out_1755007882063_3,
    output bit inj_dummy_out_1755007882112_544,
    output logic [4:0] inj_internal_out_1755007882062_456,
    output reg [3:0] inj_mux_out_1755007882063_907,
    output logic inj_o_out_1755007882077_179,
    output wire inj_out_1755007882072_184,
    output logic [3:0] inj_out_1755007882090_286,
    output bit inj_out_1755007882095_297,
    output logic inj_out_c_1755007882079_665,
    output logic inj_out_cmp_1755007882098_316,
    output logic [15:0] inj_out_concat_1755007882071_498,
    output logic [7:0] inj_out_ops_1755007882098_480,
    output logic [7:0] inj_out_reg_d_1755007882116_569,
    output reg inj_out_res_1755007882062_844,
    output reg inj_out_res_1755007882084_213,
    output reg inj_out_res_1755007882101_545,
    output bit inj_out_tc_1755007882087_122,
    output int inj_out_val_1755007882062_148,
    output int inj_out_val_1755007882121_186,
    output logic [7:0] inj_out_vec_1755007882074_585,
    output logic inj_task_out_1755007882082_937
);
    // BEGIN: unknown_class_pkg_diag_mod_ts1755007882062
    // BEGIN: case_single_default_after_item_ts1755007882062
    // BEGIN: cu_base_ts1755007882062
    // BEGIN: case_priority_overlapping_mod_ts1755007882062
    // BEGIN: mixed_conn_child_ts1755007882063
    logic dummy_internal_ts1755007882063;
        // BEGIN: deep_comb_assign_chain_ts1755007882069
        logic [15:0] t1_ts1755007882064, t2_ts1755007882064, t3_ts1755007882064, t4_ts1755007882064, t5_ts1755007882064, t6_ts1755007882064, t7_ts1755007882064, t8_ts1755007882064, t9_ts1755007882064, t10_ts1755007882064;
        logic [15:0] t11_ts1755007882064, t12_ts1755007882064, t13_ts1755007882064, t14_ts1755007882064, t15_ts1755007882064, t16_ts1755007882064, t17_ts1755007882064, t18_ts1755007882064, t19_ts1755007882064, t20_ts1755007882064;
        logic [15:0] t21_ts1755007882064, t22_ts1755007882064, t23_ts1755007882064, t24_ts1755007882064, t25_ts1755007882064, t26_ts1755007882064, t27_ts1755007882064, t28_ts1755007882064, t29_ts1755007882064, t30_ts1755007882064;
        logic [15:0] t31_ts1755007882064, t32_ts1755007882064, t33_ts1755007882064, t34_ts1755007882064, t35_ts1755007882064, t36_ts1755007882064, t37_ts1755007882064, t38_ts1755007882064, t39_ts1755007882064, t40_ts1755007882064;
            // BEGIN: named_block_logic_ts1755007882078
            logic r_internal_ts1755007882078;
            logic r_temp_ts1755007882078;
                // BEGIN: mod_statement_block_var_ts1755007882080
                always_comb begin : block_with_vars
                    int   block_local_int_ts1755007882079;
                    logic [7:0] block_local_logic_ts1755007882079;
                        // BEGIN: Module_BasicSyntax_ts1755007882098
                        logic [7:0] temp_ts1755007882098;
                            // BEGIN: invalid_this_diag_mod_ts1755007882121
                            assign inj_out_val_1755007882121_186 = block_local_int_ts1755007882079;
                            // END: invalid_this_diag_mod_ts1755007882121

                            // BEGIN: split_conditional_nb_ts1755007882116
                            always @(posedge clk) begin
                                if (inj_dummy_in_1755007882063_689) begin
                                    inj_out_reg_d_1755007882116_569 <= block_local_logic_ts1755007882079;
                                end else begin
                                    inj_out_reg_d_1755007882116_569 <= inj_data_in_1755007882062_441;
                                end
                            end
                            // END: split_conditional_nb_ts1755007882116

                            // BEGIN: module_finish_numbers_ts1755007882112
                            parameter p_finish_0 = 0;
                            parameter p_finish_1 = 1;
                            parameter p_finish_2 = 2;
                            parameter p_finish_other_3 = 3;
                            parameter p_finish_large_100 = 100;
                            parameter p_finish_neg_minus1 = -1;
                            localparam lp_finish_0 = 0;
                            localparam lp_finish_1 = 1;
                            localparam lp_finish_2 = 2;
                            localparam lp_finish_other_5 = 5;
                            localparam lp_finish_neg_minus10 = -10;
                            assign inj_dummy_out_1755007882112_544 = inj_in_tc_1755007882087_611;
                            // END: module_finish_numbers_ts1755007882112

                            // BEGIN: module_conditional_write_ts1755007882105
                            cond_if cif_inst();
                            always_comb begin
                                if (r_temp_ts1755007882078) begin
                                    cif_inst.control_reg = t1_ts1755007882064;
                                end else begin
                                    cif_inst.control_reg = 16'h0;
                                end
                                inj_control_status_1755007882105_250 = (cif_inst.control_reg != 16'h0);
                            end
                            // END: module_conditional_write_ts1755007882105

                            // BEGIN: case_empty_statement_ts1755007882101
                            always_comb begin
                                inj_out_res_1755007882101_545 = 1'b0;
                                case (inj_in_val_1755007882062_216)
                                    2'b00: inj_out_res_1755007882101_545 = 1'b1;
                                    2'b01: ;
                                    2'b10: inj_out_res_1755007882101_545 = 1'b0;
                                    default: inj_out_res_1755007882101_545 = 1'b1;
                                endcase
                            end
                            // END: case_empty_statement_ts1755007882101

                        always_comb begin
                            temp_ts1755007882098 = block_local_logic_ts1755007882079 + inj_data_in_1755007882062_441;
                        end
                        assign inj_out_ops_1755007882098_480 = (block_local_logic_ts1755007882079 & inj_data_in_1755007882062_441) | (block_local_logic_ts1755007882079 ^ inj_data_in_1755007882062_441);
                        assign inj_out_cmp_1755007882098_316 = (block_local_logic_ts1755007882079 == inj_data_in_1755007882062_441);
                        // END: Module_BasicSyntax_ts1755007882098

                        BindSimpleModule BindSimpleModule_inst_1755007882095_5688 (
                            .in(inj_in_tc_1755007882087_611),
                            .out(inj_out_1755007882095_297)
                        );
                        // BEGIN: mismatched_width_unhandled_ts1755007882090
                        assign inj_out_1755007882090_286 = inj_in_b_1755007882071_771;
                        // END: mismatched_width_unhandled_ts1755007882090

                        // BEGIN: TopConfigExample_ts1755007882087
                        Module_ConfigKeywords i_cfg (.cfg_in(inj_in_tc_1755007882087_611), .cfg_out(inj_out_tc_1755007882087_122));
                        // END: TopConfigExample_ts1755007882087

                        // BEGIN: casez_xz_ts1755007882084
                        always_comb begin
                            inj_out_res_1755007882084_213 = 1'b0;
                            casez (inj_in_val_1755007882084_769)
                                3'b1??: inj_out_res_1755007882084_213 = 1'b1;
                                3'b0z?: inj_out_res_1755007882084_213 = 1'b0;
                                default: inj_out_res_1755007882084_213 = 1'b1;
                            endcase
                        end
                        // END: casez_xz_ts1755007882084

                        // BEGIN: task_example_ts1755007882082
                        task automatic process_data (input logic data);
                            logic temp_ts1755007882082;
                            temp_ts1755007882082 = data; 
                        endtask 
                        assign inj_task_out_1755007882082_937 = r_internal_ts1755007882078;
                        // END: task_example_ts1755007882082

                    block_local_int_ts1755007882079   = r_internal_ts1755007882078 ? 10 : 20;
                    block_local_logic_ts1755007882079 = block_local_int_ts1755007882079;
                    inj_out_c_1755007882079_665             = block_local_logic_ts1755007882079[0];
                end
                // END: mod_statement_block_var_ts1755007882080

            always_comb begin : my_combinational_block
                r_temp_ts1755007882078 = dummy_internal_ts1755007882063 & inj_dummy_in_1755007882063_689;
                r_internal_ts1755007882078 = r_temp_ts1755007882078;
                inj_o_out_1755007882077_179 = r_internal_ts1755007882078;
            end
            // END: named_block_logic_ts1755007882078

            SimpleLoopExample SimpleLoopExample_inst_1755007882074_4314 (
                .in_vec(inj_data_in_1755007882062_441),
                .out_vec(inj_out_vec_1755007882074_585)
            );
            // BEGIN: mod_simple_ts1755007882072
            assign inj_out_1755007882072_184 = reset;
            // END: mod_simple_ts1755007882072

            // BEGIN: ComplexConversions_ts1755007882071
            always_comb begin
                inj_out_concat_1755007882071_498 = {inj_data_in_1755007882062_441, inj_in_b_1755007882071_771};
            end
            // END: ComplexConversions_ts1755007882071

        always_comb begin
            t1_ts1755007882064 = inj_dcac_start_val_1755007882064_305 + 1;
            t2_ts1755007882064 = t1_ts1755007882064 * 2;
            t3_ts1755007882064 = t2_ts1755007882064 - 3;
            t4_ts1755007882064 = t3_ts1755007882064 ^ 4;
            t5_ts1755007882064 = t4_ts1755007882064 | 5;
            t6_ts1755007882064 = t5_ts1755007882064 & 6;
            t7_ts1755007882064 = t6_ts1755007882064 + 7;
            t8_ts1755007882064 = t7_ts1755007882064 - 8;
            t9_ts1755007882064 = t8_ts1755007882064 ^ 9;
            t10_ts1755007882064 = t9_ts1755007882064 | 10;
            t11_ts1755007882064 = t10_ts1755007882064 & 11;
            t12_ts1755007882064 = t11_ts1755007882064 + 12;
            t13_ts1755007882064 = t12_ts1755007882064 - 13;
            t14_ts1755007882064 = t13_ts1755007882064 ^ 14;
            t15_ts1755007882064 = t14_ts1755007882064 | 15;
            t16_ts1755007882064 = t15_ts1755007882064 + 16;
            t17_ts1755007882064 = t16_ts1755007882064 * 17;
            t18_ts1755007882064 = t17_ts1755007882064 - 18;
            t19_ts1755007882064 = t18_ts1755007882064 ^ 19;
            t20_ts1755007882064 = t19_ts1755007882064 | 20;
            t21_ts1755007882064 = t20_ts1755007882064 + 1;
            t22_ts1755007882064 = t21_ts1755007882064 * 2;
            t23_ts1755007882064 = t22_ts1755007882064 - 3;
            t24_ts1755007882064 = t23_ts1755007882064 ^ 4;
            t25_ts1755007882064 = t24_ts1755007882064 | 5;
            t26_ts1755007882064 = t25_ts1755007882064 & 6;
            t27_ts1755007882064 = t26_ts1755007882064 + 7;
            t28_ts1755007882064 = t27_ts1755007882064 - 8;
            t29_ts1755007882064 = t28_ts1755007882064 ^ 9;
            t30_ts1755007882064 = t29_ts1755007882064 | 10;
            t31_ts1755007882064 = t30_ts1755007882064 & 11;
            t32_ts1755007882064 = t31_ts1755007882064 + 12;
            t33_ts1755007882064 = t32_ts1755007882064 - 13;
            t34_ts1755007882064 = t33_ts1755007882064 ^ 14;
            t35_ts1755007882064 = t34_ts1755007882064 | 15;
            t36_ts1755007882064 = t35_ts1755007882064 + 16;
            t37_ts1755007882064 = t36_ts1755007882064 * 17;
            t38_ts1755007882064 = t37_ts1755007882064 - 18;
            t39_ts1755007882064 = t38_ts1755007882064 ^ 19;
            t40_ts1755007882064 = t39_ts1755007882064 | 20;
            inj_dcac_end_val_1755007882064_990 = t40_ts1755007882064;
        end
        // END: deep_comb_assign_chain_ts1755007882069

        // BEGIN: Comb_Case_ts1755007882063
        always_comb begin
            case (inj_sel_1755007882063_44)
                2'b00: inj_mux_out_1755007882063_907 = inj_in0_1755007882063_31;
                2'b01: inj_mux_out_1755007882063_907 = inj_in1_1755007882063_351;
                2'b10: inj_mux_out_1755007882063_907 = inj_in2_1755007882063_346;
                default: inj_mux_out_1755007882063_907 = inj_in3_1755007882063_982;
            endcase
        end
        // END: Comb_Case_ts1755007882063

    always_comb dummy_internal_ts1755007882063 = |inj_data_in_1755007882062_441 | inj_dummy_in_1755007882063_689;
    assign inj_dummy_out_1755007882063_3 = dummy_internal_ts1755007882063;
    // END: mixed_conn_child_ts1755007882063

    always @* begin
        priority casez (inj_in_val_1755007882062_216)
            2'b1?: inj_internal_out_1755007882062_456 = 5;
            2'b?1: inj_internal_out_1755007882062_456 = 6;  
            2'b0?: inj_internal_out_1755007882062_456 = 7;
            2'b?0: inj_internal_out_1755007882062_456 = 8;  
            default: inj_internal_out_1755007882062_456 = 9;
        endcase
    end
    // END: case_priority_overlapping_mod_ts1755007882062

    assign inj_data_out_1755007882062_208 = inj_data_in_1755007882062_441;
    // END: cu_base_ts1755007882062

    always_comb begin
        inj_out_res_1755007882062_844 = 1'b0;
        case (inj_in_val_1755007882062_216)
            2'b01: inj_out_res_1755007882062_844 = 1'b1;
            default: inj_out_res_1755007882062_844 = 1'b0;
            2'b10: inj_out_res_1755007882062_844 = 1'b1;
        endcase
    end
    // END: case_single_default_after_item_ts1755007882062

    assign inj_out_val_1755007882062_148 = inj_in_val_1755007882062_762;
    // END: unknown_class_pkg_diag_mod_ts1755007882062
endmodule

