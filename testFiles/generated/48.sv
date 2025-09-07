module Parameterized #(
    parameter int WIDTH = 8
) (
    input logic [7:0] din,
    output logic [7:0] dout
);
    assign dout = din;
endmodule

module SimpleAssign (
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    assign out_data = in_data;
endmodule

module loop_unroll_limit_test (
    input logic [1:0] large_data_in,
    output logic [7:0] large_sum_out
);
    logic [7:0] current_large_sum;
    always_comb begin
        current_large_sum = 8'h00;
        for (int m = 0; m < 40; m = m + 1) begin 
            current_large_sum = current_large_sum + large_data_in[0];
            current_large_sum = current_large_sum + large_data_in[1];
            current_large_sum = current_large_sum + 1;
        end
        large_sum_out = current_large_sum;
    end
endmodule

module snippet #(
    parameter int P_PORT_VAL = 25
) (
    input wire clk,
    input logic inj_in1_1755004219738_754,
    input bit [3:0] inj_in1_1755004219740_752,
    input bit [3:0] inj_in2_1755004219740_116,
    input wire [7:0] inj_in_func_a_1755004219742_963,
    input wire [7:0] inj_in_func_b_1755004219742_9,
    input logic [7:0] inj_in_val_e_1755004219747_351,
    input logic [1:0] inj_large_data_in_1755004219739_56,
    input logic [7:0] inj_start_val_i_1755004219738_202,
    input int inj_val_false_1755004219745_141,
    input int inj_val_true_1755004219745_575,
    input wire reset,
    output logic [7:0] inj_data_out_1755004219752_248,
    output logic [7:0] inj_dout_1755004219760_218,
    output logic [7:0] inj_large_sum_out_1755004219739_756,
    output logic [7:0] inj_o_sum_1755004219743_596,
    output int inj_o_val_1755004219749_158,
    output logic inj_out1_1755004219738_757,
    output bit [3:0] inj_out1_1755004219740_471,
    output logic [7:0] inj_out1_z_1755004219755_850,
    output bit [3:0] inj_out2_1755004219740_744,
    output logic [7:0] inj_out2_z_1755004219755_39,
    output logic [7:0] inj_out_data_1755004219764_704,
    output logic [7:0] inj_out_func_result_1755004219742_992,
    output logic inj_out_l_1755004219771_734,
    output logic [7:0] inj_out_v_1755004219739_937,
    output int inj_out_val_1755004219745_101,
    output int inj_out_val_1755004219768_452,
    output logic [7:0] inj_out_val_e_1755004219747_455,
    output logic inj_status_e_1755004219747_571,
    output logic [15:0] inj_sum_out_i_1755004219738_542
);
    // BEGIN: split_for_loop_ts1755004219738
    // BEGIN: ModuleLineDirective_ts1755004219739
    logic internal_sig_a_ts1755004219739;
    logic internal_sig_b_ts1755004219739;
    logic unused_line_var_ts1755004219739;
        // BEGIN: ModuleFF_ts1755004219741
        parameter int MAX_COUNT = 10;
        localparam int START_VAL = 5;
        logic [3:0] ff_reg_ts1755004219741;
        integer unused_int_var_ts1755004219741;
            // BEGIN: module_function_ts1755004219742
            function automatic [7:0] add_and_subtract;
            input [7:0] val1;
            input [7:0] val2;
            reg [7:0] temp_ts1755004219742;
                // BEGIN: split_mixed_cond_seq_ts1755004219747
                logic [7:0] temp_val_e_ts1755004219747;
                    // BEGIN: mod_automatic_task_ts1755004219749
                    task automatic update_val(input int in_v, output int out_v);
                        out_v = in_v * 2;
                    endtask
                    always_comb begin
                        int temp_val_ts1755004219749;
                            // BEGIN: SequentialLogic_ts1755004219752
                            logic [7:0] internal_reg_ts1755004219752;
                                // BEGIN: LintLatch_ts1755004219772
                                always_comb begin
                                    if (inj_in1_1755004219738_754) begin
                                        inj_out_l_1755004219771_734 = internal_sig_b_ts1755004219739;
                                    end else begin
                                        inj_out_l_1755004219771_734 = 1'b0; 
                                    end
                                end
                                // END: LintLatch_ts1755004219772

                                // BEGIN: local_not_allowed_diag_mod_ts1755004219768
                                assign inj_out_val_1755004219768_452 = inj_val_false_1755004219745_141;
                                // END: local_not_allowed_diag_mod_ts1755004219768

                                SimpleAssign SimpleAssign_inst_1755004219764_3359 (
                                    .in_data(temp_val_e_ts1755004219747),
                                    .out_data(inj_out_data_1755004219764_704)
                                );
                                Parameterized Parameterized_inst_1755004219760_2282 (
                                    .din(temp_val_e_ts1755004219747),
                                    .dout(inj_dout_1755004219760_218)
                                );
                                // BEGIN: split_diff_vars_branches_ts1755004219755
                                always @(posedge clk) begin
                                    if (unused_line_var_ts1755004219739) begin
                                        inj_out1_z_1755004219755_850 <= inj_in_val_e_1755004219747_351;
                                    end else begin
                                        inj_out2_z_1755004219755_39 <= temp_val_e_ts1755004219747;
                                    end
                                end
                                // END: split_diff_vars_branches_ts1755004219755

                            always @(posedge clk or negedge reset) begin
                                if (~reset) begin
                                    internal_reg_ts1755004219752 <= 8'h00;
                                end else begin
                                    internal_reg_ts1755004219752 <= inj_in_val_e_1755004219747_351;
                                end
                            end
                            assign inj_data_out_1755004219752_248 = internal_reg_ts1755004219752;
                            // END: SequentialLogic_ts1755004219752

                        update_val(inj_val_false_1755004219745_141, temp_val_ts1755004219749);
                        inj_o_val_1755004219749_158 = temp_val_ts1755004219749;
                    end
                    // END: mod_automatic_task_ts1755004219749

                always @(posedge clk) begin
                    temp_val_e_ts1755004219747 <= inj_in_val_e_1755004219747_351 + 5;
                    if (internal_sig_a_ts1755004219739) begin
                        inj_out_val_e_1755004219747_455 <= temp_val_e_ts1755004219747;
                        inj_status_e_1755004219747_571 <= 1;
                    end else begin
                        inj_out_val_e_1755004219747_455 <= inj_start_val_i_1755004219738_202;
                        inj_status_e_1755004219747_571 <= 0;
                    end
                end
                // END: split_mixed_cond_seq_ts1755004219747

                // BEGIN: ConditionalOps_ts1755004219745
                assign inj_out_val_1755004219745_101 = internal_sig_a_ts1755004219739 ? inj_val_true_1755004219745_575 : inj_val_false_1755004219745_141;
                // END: ConditionalOps_ts1755004219745

                // BEGIN: param_local_port_ts1755004219743
                localparam int LP_BODY_VAL = 125;
                localparam int LP_CALCULATED = P_PORT_VAL + LP_BODY_VAL;
                always_comb begin
                    if (reset) begin
                        inj_o_sum_1755004219743_596 = 0;
                    end else begin
                        inj_o_sum_1755004219743_596 = LP_CALCULATED;
                    end
                end
                // END: param_local_port_ts1755004219743

            begin
            temp_ts1755004219742 = val1 + val2;
            add_and_subtract = temp_ts1755004219742 - 1;
            end
            endfunction
            always_comb begin
            inj_out_func_result_1755004219742_992 = add_and_subtract(inj_in_func_a_1755004219742_963, inj_in_func_b_1755004219742_9);
            end
            // END: module_function_ts1755004219742

        always_ff @(posedge clk or posedge reset) begin
            if (reset) begin
                ff_reg_ts1755004219741 <= START_VAL;
                inj_out1_1755004219740_471 <= '0;
                inj_out2_1755004219740_744 <= '0;
                unused_int_var_ts1755004219741 <= 0;
            end else begin
                case ({inj_in1_1755004219740_752, inj_in2_1755004219740_116})
                    8'h00: ff_reg_ts1755004219741 <= ff_reg_ts1755004219741;
                    8'h01: ff_reg_ts1755004219741 <= inj_in1_1755004219740_752 + inj_in2_1755004219740_116;
                    default: ff_reg_ts1755004219741 <= MAX_COUNT;
                endcase
                inj_out1_1755004219740_471 <= ff_reg_ts1755004219741;
                inj_out2_1755004219740_744 <= {inj_in1_1755004219740_752[0], inj_in1_1755004219740_752[0], inj_in1_1755004219740_752[0], inj_in1_1755004219740_752[0]} | {inj_in2_1755004219740_116[3], inj_in2_1755004219740_116[2], inj_in2_1755004219740_116[1], inj_in2_1755004219740_116[0]};
            end
        end
        // END: ModuleFF_ts1755004219741

        // BEGIN: ModVectorAdd_ts1755004219739
        assign inj_out_v_1755004219739_937 = inj_start_val_i_1755004219738_202 + 8'h01;
        // END: ModVectorAdd_ts1755004219739

        loop_unroll_limit_test loop_unroll_limit_test_inst_1755004219739_1996 (
            .large_data_in(inj_large_data_in_1755004219739_56),
            .large_sum_out(inj_large_sum_out_1755004219739_756)
        );
    `line 100 "virtual_file_A.sv" 1
    assign internal_sig_a_ts1755004219739 = inj_in1_1755004219738_754;
    `line 20 "virtual_file_B.sv" 1
    assign internal_sig_b_ts1755004219739 = ~internal_sig_a_ts1755004219739;
    assign unused_line_var_ts1755004219739 = 1'b1;
    `line 150 "virtual_file_A.sv" 2
    assign inj_out1_1755004219738_757 = internal_sig_b_ts1755004219739;
    `line 1 "original_file.sv" 0
    // END: ModuleLineDirective_ts1755004219739

    always @(posedge clk) begin
        inj_sum_out_i_1755004219738_542 <= 0;
        for (int i = 0; i < 4; i = i + 1) begin
            inj_sum_out_i_1755004219738_542 <= inj_sum_out_i_1755004219738_542 + inj_start_val_i_1755004219738_202 + i;
        end
    end
    // END: split_for_loop_ts1755004219738
endmodule

