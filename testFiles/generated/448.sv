module module_latch (
    input wire [7:0] in_latch_data,
    input wire in_latch_en,
    output reg [7:0] out_latch_reg
);
    always_latch begin
    if (in_latch_en) begin
        out_latch_reg = in_latch_data;
    end
    end
endmodule

module unsupported_logand_expr (
    input logic [7:0] in_a_m9,
    input logic [7:0] in_b_m9,
    output logic out_m9
);
    logic [7:0] var_m9;
    always_comb begin
        var_m9 = in_a_m9;
        if ((var_m9 > 10) && (in_b_m9 < 5)) begin
            out_m9 = 1;
        end else begin
            out_m9 = 0;
        end
        var_m9++;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755007903907_407,
    input int inj_b_1755007903907_875,
    input bit inj_cfg_in_1755007903913_72,
    input wire [1:0] inj_dtl_action_sel_1755007903917_83,
    input wire [7:0] inj_dtl_data_b_1755007903917_60,
    input logic [7:0] inj_in3_1755007903909_722,
    input wire [3:0] inj_in_a_1755007903924_121,
    input wire [3:0] inj_in_b_1755007903924_35,
    input wire [7:0] inj_in_latch_data_1755007903914_262,
    input logic [2:0] inj_index_1755007903910_97,
    input logic [7:0] inj_op1_u_1755007903908_90,
    input logic [7:0] inj_op2_u_1755007903908_882,
    input wire [63:0] inj_wide_a_1755007903922_719,
    input wire [63:0] inj_wide_b_1755007903922_410,
    input wire reset,
    output bit inj_cfg_out_1755007903913_607,
    output wire [127:0] inj_concat_out_1755007903922_815,
    output logic [7:0] inj_diff_u_1755007903908_599,
    output logic [7:0] inj_dtl_result_reg_1755007903917_256,
    output logic [7:0] inj_out_1755007903909_331,
    output logic inj_out_1755007903910_477,
    output logic inj_out_a_1755007903907_992,
    output logic inj_out_a_1755007903915_892,
    output int inj_out_b_1755007903907_792,
    output int inj_out_b_1755007903915_234,
    output logic [15:0] inj_out_concat_1755007903924_362,
    output logic [7:0] inj_out_if_else_1755007903924_607,
    output reg [7:0] inj_out_latch_reg_1755007903914_946,
    output logic inj_out_m9_1755007903909_911,
    output int inj_out_val_1755007903912_440,
    output logic [7:0] inj_prod_u_1755007903908_793,
    output wire [7:0] inj_reduce_xor_out_1755007903922_186,
    output logic [7:0] inj_result_m_1755007903911_736,
    output logic inj_sum_1755007903908_133,
    output logic [7:0] inj_sum_u_1755007903908_472,
    output wire [63:0] inj_wide_sum_1755007903922_881
);
    // BEGIN: ModuleBasic_ts1755007903907
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c_ts1755007903907;
    int   d_ts1755007903907;
    always_comb begin
        logic temp_v_ts1755007903907;
            // BEGIN: ModuleBasic_ts1755007903916
            parameter int P1  = 10;
            localparam int LP1 = 20;
            logic c_ts1755007903916;
            int   d_ts1755007903916;
            always_comb begin
                logic temp_v_ts1755007903916;
                    // BEGIN: deep_task_logic_ts1755007903920
                    task automatic perform_action;
                        input [7:0] in_a;
                        input [7:0] in_b;
                        input [1:0] action;
                        output logic [7:0] calculated_res_ts1755007903919;
                        logic [7:0] temp_task_calc_ts1755007903919;
                        if (action[0]) begin
                            if (action[1]) begin
                                temp_task_calc_ts1755007903919 = in_a + in_b;
                            end else begin
                                temp_task_calc_ts1755007903919 = in_a - in_b;
                            end
                        end else begin
                            if (action[1]) begin
                                temp_task_calc_ts1755007903919 = in_a & in_b;
                            end else begin
                                temp_task_calc_ts1755007903919 = in_a | in_b;
                            end
                        end
                        case (temp_task_calc_ts1755007903919[1:0])
                            2'b00: calculated_res_ts1755007903919 = temp_task_calc_ts1755007903919 ^ 8'hFF;
                            2'b01: calculated_res_ts1755007903919 = temp_task_calc_ts1755007903919 + 1;
                            2'b10: calculated_res_ts1755007903919 = temp_task_calc_ts1755007903919 - 1;
                            default: calculated_res_ts1755007903919 = temp_task_calc_ts1755007903919;
                        endcase
                    endtask
                    always_ff @(posedge clk or negedge reset) begin
                        if (!reset) begin
                            inj_dtl_result_reg_1755007903917_256 <= 8'd0;
                        end else begin
                            logic [7:0] next_dtl_result_ts1755007903919;
                                // BEGIN: module_concat_if_ts1755007903925
                                always_comb begin
                                inj_out_concat_1755007903924_362 = {inj_in_a_1755007903924_121, inj_in_b_1755007903924_35, inj_dtl_data_b_1755007903917_60};
                                if (reset) begin
                                    inj_out_if_else_1755007903924_607 = inj_dtl_data_b_1755007903917_60;
                                end else begin
                                    inj_out_if_else_1755007903924_607 = {inj_in_a_1755007903924_121, inj_in_b_1755007903924_35};
                                end
                                end
                                // END: module_concat_if_ts1755007903925

                                // BEGIN: wide_bus_ops_ts1755007903923
                                assign inj_wide_sum_1755007903922_881 = inj_wide_a_1755007903922_719 + inj_wide_b_1755007903922_410;
                                assign inj_reduce_xor_out_1755007903922_186 = ^inj_wide_a_1755007903922_719[63:0];
                                assign inj_concat_out_1755007903922_815 = {inj_wide_a_1755007903922_719, inj_wide_b_1755007903922_410};
                                // END: wide_bus_ops_ts1755007903923

                            if (clk) begin
                                perform_action(inj_in_latch_data_1755007903914_262, inj_dtl_data_b_1755007903917_60, inj_dtl_action_sel_1755007903917_83, next_dtl_result_ts1755007903919);
                            end else begin
                                next_dtl_result_ts1755007903919 = inj_dtl_result_reg_1755007903917_256;
                            end
                            inj_dtl_result_reg_1755007903917_256 <= next_dtl_result_ts1755007903919;
                        end
                    end
                    // END: deep_task_logic_ts1755007903920

                temp_v_ts1755007903916 = d_ts1755007903916;
                c_ts1755007903916      = temp_v_ts1755007903916;
            end
            assign inj_out_a_1755007903915_892 = temp_v_ts1755007903907;
            assign d_ts1755007903916     = d_ts1755007903907;
            assign inj_out_b_1755007903915_234 = d_ts1755007903916 + P1 + LP1;
            // END: ModuleBasic_ts1755007903916

            module_latch module_latch_inst_1755007903914_6907 (
                .in_latch_en(clk),
                .out_latch_reg(inj_out_latch_reg_1755007903914_946),
                .in_latch_data(inj_in_latch_data_1755007903914_262)
            );
            // BEGIN: Module_ConfigKeywords_ts1755007903913
            assign inj_cfg_out_1755007903913_607 = inj_cfg_in_1755007903913_72;
            // END: Module_ConfigKeywords_ts1755007903913

            // BEGIN: definition_used_diag_mod_ts1755007903912
            assign inj_out_val_1755007903912_440 = inj_b_1755007903907_875;
            // END: definition_used_diag_mod_ts1755007903912

            // BEGIN: split_nested_if_ts1755007903911
            always @(posedge clk) begin
                if (temp_v_ts1755007903907) begin
                    if (c_ts1755007903907) begin
                        inj_result_m_1755007903911_736 <= inj_op2_u_1755007903908_882;
                    end else begin
                        inj_result_m_1755007903911_736 <= inj_op1_u_1755007903908_90;
                    end
                end else begin
                    inj_result_m_1755007903911_736 <= inj_in3_1755007903909_722;
                end
            end
            // END: split_nested_if_ts1755007903911

            // BEGIN: variable_sel_mux_ts1755007903910
            assign inj_out_1755007903910_477 = inj_in3_1755007903909_722[inj_index_1755007903910_97];
            // END: variable_sel_mux_ts1755007903910

            unsupported_logand_expr unsupported_logand_expr_inst_1755007903909_4142 (
                .in_b_m9(inj_op2_u_1755007903908_882),
                .out_m9(inj_out_m9_1755007903909_911),
                .in_a_m9(inj_op1_u_1755007903908_90)
            );
            // BEGIN: bitwise_ops_ts1755007903909
            assign inj_out_1755007903909_331 = (inj_op1_u_1755007903908_90 & inj_op2_u_1755007903908_882) | (~inj_in3_1755007903909_722) ^ (inj_op1_u_1755007903908_90 << 2) >> 1;
            // END: bitwise_ops_ts1755007903909

            // BEGIN: split_arith_blocking_ts1755007903908
            always @(*) begin
                inj_sum_u_1755007903908_472 = inj_op1_u_1755007903908_90 + inj_op2_u_1755007903908_882;
                inj_diff_u_1755007903908_599 = inj_op1_u_1755007903908_90 - inj_op2_u_1755007903908_882;
                inj_prod_u_1755007903908_793 = inj_op1_u_1755007903908_90 * inj_op2_u_1755007903908_882;
            end
            // END: split_arith_blocking_ts1755007903908

            // BEGIN: simple_adder_ts1755007903908
            assign inj_sum_1755007903908_133 = temp_v_ts1755007903907 + c_ts1755007903907;
            // END: simple_adder_ts1755007903908

        temp_v_ts1755007903907 = d_ts1755007903907;
        c_ts1755007903907      = temp_v_ts1755007903907;
    end
    assign inj_out_a_1755007903907_992 = inj_a_1755007903907_407;
    assign d_ts1755007903907     = inj_b_1755007903907_875;
    assign inj_out_b_1755007903907_792 = d_ts1755007903907 + P1 + LP1;
    // END: ModuleBasic_ts1755007903907
endmodule

