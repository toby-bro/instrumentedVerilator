module case_single_default_after_item (
    input logic [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b01: out_res = 1'b1;
            default: out_res = 1'b0;
            2'b10: out_res = 1'b1;
        endcase
    end
endmodule

module mod_comb_logic (
    input logic a,
    input logic b,
    output logic y
);
    always_comb begin
        y = a & b;
    end
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

module simple_and_gate (
    input logic in1,
    input logic in2,
    output logic out
);
    assign out = in1 & in2;
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007789075_972,
    input logic inj_dummy_in_non_ansi_1755007789077_681,
    input logic [7:0] inj_in1_1755007789076_318,
    input logic [7:0] inj_in2_1755007789076_848,
    input int inj_in_val_1755007789076_788,
    input logic [2:0] inj_mode_1755007789078_866,
    input logic inj_named_conn_in_1755007789077_364,
    input logic [63:0] inj_wide_a_1755007789090_145,
    input logic [63:0] inj_wide_b_1755007789090_228,
    input logic [63:0] inj_wide_c_1755007789090_570,
    input wire reset,
    output logic [7:0] inj_default_out_1755007789093_212,
    output logic [7:0] inj_diff_v_1755007789103_92,
    output logic inj_dummy_out_non_ansi_1755007789077_851,
    output logic [4:0] inj_internal_out_1755007789075_823,
    output wire inj_loop_out_1755007789076_425,
    output logic inj_named_conn_out_1755007789077_868,
    output wire inj_o_c_1755007789078_935,
    output logic inj_o_p_and_1755007789087_171,
    output logic inj_o_p_xor_1755007789087_494,
    output int inj_o_val_1755007789096_650,
    output logic [7:0] inj_out1_1755007789099_215,
    output logic [7:0] inj_out2_1755007789099_736,
    output logic inj_out_1755007789076_109,
    output logic inj_out_1755007789107_153,
    output logic [1:0] inj_out_bits_1755007789111_240,
    output reg inj_out_res_1755007789081_576,
    output int inj_out_val_1755007789076_582,
    output logic [7:0] inj_prod_v_1755007789103_990,
    output logic [7:0] inj_res_1755007789078_273,
    output logic inj_result_out_1755007789084_370,
    output logic [7:0] inj_sum_v_1755007789103_787,
    output logic [63:0] inj_wide_out_1755007789090_103,
    output logic inj_y_1755007789117_299
);
    // BEGIN: case_priority_overlapping_mod_ts1755007789075
    // BEGIN: unknown_class_pkg_diag_mod_ts1755007789076
    // BEGIN: reduction_ops_ts1755007789076
    // BEGIN: Comb_Loop_ts1755007789076
    wire loop_wire1_ts1755007789076;
    wire loop_wire2_ts1755007789076;
        // BEGIN: explicit_non_ansi_ports_module_ts1755007789077
        input logic inj_named_conn_in_1755007789077_364_ts1755007789077;
        output logic inj_named_conn_out_1755007789077_868_ts1755007789077;
        input logic inj_dummy_in_non_ansi_1755007789077_681_ts1755007789077;
        output logic inj_dummy_out_non_ansi_1755007789077_851_ts1755007789077;
            // BEGIN: module_simple_ts1755007789078
            wire internal_xor_res_ts1755007789078;
                // BEGIN: mod_automatic_task_ts1755007789096
                task automatic update_val(input int in_v, output int out_v);
                    out_v = in_v * 2;
                endtask
                always_comb begin
                    int temp_val_ts1755007789096;
                        // BEGIN: ModuleComb_ts1755007789099
                        logic [7:0] internal_wire_ts1755007789099;
                            // BEGIN: cast_select_demo_ts1755007789111
                            logic [7:0] internal_ts1755007789111;
                                mod_comb_logic mod_comb_logic_inst_1755007789117_87 (
                                    .y(inj_y_1755007789117_299),
                                    .a(inj_dummy_out_non_ansi_1755007789077_851_ts1755007789077),
                                    .b(inj_named_conn_in_1755007789077_364)
                                );
                            always_comb begin
                                internal_ts1755007789111 = inj_in1_1755007789076_318;
                                inj_out_bits_1755007789111_240 = internal_ts1755007789111[3 -: 2];
                            end
                            // END: cast_select_demo_ts1755007789111

                            simple_and_gate simple_and_gate_inst_1755007789107_3854 (
                                .in1(inj_dummy_in_non_ansi_1755007789077_681_ts1755007789077),
                                .in2(inj_dummy_out_non_ansi_1755007789077_851_ts1755007789077),
                                .out(inj_out_1755007789107_153)
                            );
                            // BEGIN: split_arith_nb_ts1755007789103
                            always @(posedge clk) begin
                                inj_sum_v_1755007789103_787 <= inj_in2_1755007789076_848 + inj_in1_1755007789076_318;
                                inj_diff_v_1755007789103_92 <= inj_in2_1755007789076_848 - inj_in1_1755007789076_318;
                                inj_prod_v_1755007789103_990 <= inj_in2_1755007789076_848 * inj_in1_1755007789076_318;
                            end
                            // END: split_arith_nb_ts1755007789103

                        assign internal_wire_ts1755007789099 = inj_in1_1755007789076_318 + inj_in2_1755007789076_848;
                        always_comb begin
                            if (internal_wire_ts1755007789099 > 8'd128) begin
                                inj_out1_1755007789099_215 = internal_wire_ts1755007789099 - 1;
                            end else begin
                                inj_out1_1755007789099_215 = internal_wire_ts1755007789099 + 1;
                            end
                            inj_out2_1755007789099_736 = internal_wire_ts1755007789099 / 2;
                        end
                        // END: ModuleComb_ts1755007789099

                    update_val(inj_in_val_1755007789076_788, temp_val_ts1755007789096);
                    inj_o_val_1755007789096_650 = temp_val_ts1755007789096;
                end
                // END: mod_automatic_task_ts1755007789096

                // BEGIN: func_macro_defaults_ts1755007789093
                `define DEFAULT_CONST       8'hAA
                `define CALC(val, def=`DEFAULT_CONST) ((val) | (def))
                localparam logic [7:0] P_WITH_DEF     = `CALC(8'h0F);
                localparam logic [7:0] P_OVERRIDE_DEF = `CALC(8'hF0, 8'h11);
                assign inj_default_out_1755007789093_212 = inj_dummy_in_non_ansi_1755007789077_681_ts1755007789077 ? P_WITH_DEF : P_OVERRIDE_DEF;
                // END: func_macro_defaults_ts1755007789093

                // BEGIN: wide_ops_deep_ts1755007789090
                assign inj_wide_out_1755007789090_103 = (((inj_wide_a_1755007789090_145 + inj_wide_b_1755007789090_228) ^ inj_wide_c_1755007789090_570) & (~inj_wide_a_1755007789090_145 | inj_wide_b_1755007789090_228)) + (inj_wide_c_1755007789090_570 >>> 5);
                // END: wide_ops_deep_ts1755007789090

                primitive_example primitive_example_inst_1755007789088_62 (
                    .i_p2(inj_named_conn_out_1755007789077_868_ts1755007789077),
                    .o_p_and(inj_o_p_and_1755007789087_171),
                    .o_p_xor(inj_o_p_xor_1755007789087_494),
                    .i_p1(inj_dummy_out_non_ansi_1755007789077_851_ts1755007789077)
                );
                // BEGIN: nested_blocks_ts1755007789085
                always_comb begin : main_block 
                    inj_result_out_1755007789084_370 = 1'b0; 
                    if (inj_dummy_out_non_ansi_1755007789077_851_ts1755007789077) begin : inner_block1 
                        if (inj_named_conn_out_1755007789077_868_ts1755007789077) begin : inner_block2 
                            inj_result_out_1755007789084_370 = inj_dummy_in_non_ansi_1755007789077_681_ts1755007789077;
                        end 
                    end 
                end
                // END: nested_blocks_ts1755007789085

                case_single_default_after_item case_single_default_after_item_inst_1755007789081_6430 (
                    .out_res(inj_out_res_1755007789081_576),
                    .in_val(inj_case_expr_1755007789075_972)
                );
                // BEGIN: dup_nested_if_ts1755007789079
                always_comb begin
                    inj_res_1755007789078_273 = '0;
                    if (inj_mode_1755007789078_866 == 3'b001) begin
                        if (inj_in2_1755007789076_848 > inj_in1_1755007789076_318) begin
                            inj_res_1755007789078_273 = inj_in2_1755007789076_848 + inj_in1_1755007789076_318;
                        end else begin
                            inj_res_1755007789078_273 = inj_in2_1755007789076_848 - inj_in1_1755007789076_318;
                        end
                    end else if (inj_mode_1755007789078_866 == 3'b010) begin
                        if (inj_in2_1755007789076_848 > inj_in1_1755007789076_318) begin
                            inj_res_1755007789078_273 = inj_in2_1755007789076_848 + inj_in1_1755007789076_318;
                        end else begin
                            inj_res_1755007789078_273 = inj_in2_1755007789076_848 - inj_in1_1755007789076_318;
                        end
                    end else if (inj_mode_1755007789078_866 == 3'b011) begin
                        if (inj_in2_1755007789076_848 < inj_in1_1755007789076_318) begin
                            inj_res_1755007789078_273 = inj_in2_1755007789076_848 * inj_in1_1755007789076_318;
                        end else begin
                            inj_res_1755007789078_273 = inj_in2_1755007789076_848 / ((inj_in1_1755007789076_318 == 0) ? 1 : inj_in1_1755007789076_318);
                        end
                    end else if (inj_mode_1755007789078_866 == 3'b100) begin
                        if (inj_in2_1755007789076_848 != inj_in1_1755007789076_318) begin
                            if (inj_in2_1755007789076_848 > inj_in1_1755007789076_318) inj_res_1755007789078_273 = inj_in2_1755007789076_848;
                            else inj_res_1755007789078_273 = inj_in1_1755007789076_318;
                        end else begin
                            inj_res_1755007789078_273 = inj_in2_1755007789076_848 + inj_in1_1755007789076_318;
                        end
                    end
                    else begin
                        inj_res_1755007789078_273 = inj_in2_1755007789076_848 ^ inj_in1_1755007789076_318;
                    end
                end
                // END: dup_nested_if_ts1755007789079

            assign internal_xor_res_ts1755007789078 = loop_wire2_ts1755007789076 ^ clk;
            assign inj_o_c_1755007789078_935 = internal_xor_res_ts1755007789078 & loop_wire2_ts1755007789076;
            // END: module_simple_ts1755007789078

        assign inj_named_conn_out_1755007789077_868_ts1755007789077 = inj_named_conn_in_1755007789077_364_ts1755007789077;
        assign inj_dummy_out_non_ansi_1755007789077_851_ts1755007789077 = inj_dummy_in_non_ansi_1755007789077_681_ts1755007789077;
        // END: explicit_non_ansi_ports_module_ts1755007789077

    assign loop_wire1_ts1755007789076 = loop_wire2_ts1755007789076 | reset;
    assign loop_wire2_ts1755007789076 = loop_wire1_ts1755007789076; 
    assign inj_loop_out_1755007789076_425 = loop_wire1_ts1755007789076;
    // END: Comb_Loop_ts1755007789076

    assign inj_out_1755007789076_109 = &inj_in1_1755007789076_318 | ^inj_in2_1755007789076_848;
    // END: reduction_ops_ts1755007789076

    assign inj_out_val_1755007789076_582 = inj_in_val_1755007789076_788;
    // END: unknown_class_pkg_diag_mod_ts1755007789076

    always @* begin
        priority casez (inj_case_expr_1755007789075_972)
            2'b1?: inj_internal_out_1755007789075_823 = 5;
            2'b?1: inj_internal_out_1755007789075_823 = 6;  
            2'b0?: inj_internal_out_1755007789075_823 = 7;
            2'b?0: inj_internal_out_1755007789075_823 = 8;  
            default: inj_internal_out_1755007789075_823 = 9;
        endcase
    end
    // END: case_priority_overlapping_mod_ts1755007789075
endmodule

