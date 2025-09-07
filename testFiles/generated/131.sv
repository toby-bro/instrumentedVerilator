module mod_statement_block_var (
    input logic in_c,
    output logic out_c
);
    always_comb begin : block_with_vars
        int   block_local_int;
        logic [7:0] block_local_logic;
        block_local_int   = in_c ? 10 : 20;
        block_local_logic = block_local_int;
        out_c             = block_local_logic[0];
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_data_in_k_1755007796885_304,
    input wire [1:0] inj_dtl_action_sel_1755007796886_579,
    input wire [7:0] inj_dtl_data_a_1755007796886_611,
    input wire [7:0] inj_dtl_data_b_1755007796886_886,
    input logic inj_in_a_1755007796885_345,
    input logic inj_in_c_1755007796885_823,
    input wire reset,
    output logic inj_bind_out_1755007796887_310,
    output logic inj_data_out_1755007796885_730,
    output logic [7:0] inj_data_out_k_1755007796885_826,
    output logic [7:0] inj_dtl_result_reg_1755007796886_763,
    output logic inj_out_c_1755007796885_830,
    output logic inj_out_comb_1755007796885_253,
    output logic inj_out_m9_1755007796888_757,
    output logic inj_out_reg_1755007796885_119
);
    // BEGIN: ModClockedWithSimpleAssign_ts1755007796885
    logic internal_reg_ts1755007796885;
        // BEGIN: ModClockedConditional_ts1755007796885
        logic reg_data_ts1755007796885;
            // BEGIN: deep_task_logic_ts1755007796886
            task automatic perform_action;
                input [7:0] in_a;
                input [7:0] in_b;
                input [1:0] action;
                output logic [7:0] calculated_res_ts1755007796886;
                logic [7:0] temp_task_calc_ts1755007796886;
                if (action[0]) begin
                    if (action[1]) begin
                        temp_task_calc_ts1755007796886 = in_a + in_b;
                    end else begin
                        temp_task_calc_ts1755007796886 = in_a - in_b;
                    end
                end else begin
                    if (action[1]) begin
                        temp_task_calc_ts1755007796886 = in_a & in_b;
                    end else begin
                        temp_task_calc_ts1755007796886 = in_a | in_b;
                    end
                end
                case (temp_task_calc_ts1755007796886[1:0])
                    2'b00: calculated_res_ts1755007796886 = temp_task_calc_ts1755007796886 ^ 8'hFF;
                    2'b01: calculated_res_ts1755007796886 = temp_task_calc_ts1755007796886 + 1;
                    2'b10: calculated_res_ts1755007796886 = temp_task_calc_ts1755007796886 - 1;
                    default: calculated_res_ts1755007796886 = temp_task_calc_ts1755007796886;
                endcase
            endtask
            always_ff @(posedge clk or negedge reset) begin
                if (!reset) begin
                    inj_dtl_result_reg_1755007796886_763 <= 8'd0;
                end else begin
                    logic [7:0] next_dtl_result_ts1755007796886;
                        // BEGIN: unsupported_logand_expr_ts1755007796889
                        logic [7:0] var_m9_ts1755007796888;
                        always_comb begin
                            var_m9_ts1755007796888 = next_dtl_result_ts1755007796886;
                            if ((var_m9_ts1755007796888 > 10) && (inj_data_in_k_1755007796885_304 < 5)) begin
                                inj_out_m9_1755007796888_757 = 1;
                            end else begin
                                inj_out_m9_1755007796888_757 = 0;
                            end
                            var_m9_ts1755007796888++;
                        end
                        // END: unsupported_logand_expr_ts1755007796889

                        // BEGIN: bind_module_ts1755007796887
                        assign inj_bind_out_1755007796887_310 = internal_reg_ts1755007796885;
                        // END: bind_module_ts1755007796887

                    if (reset) begin
                        perform_action(inj_dtl_data_a_1755007796886_611, inj_dtl_data_b_1755007796886_886, inj_dtl_action_sel_1755007796886_579, next_dtl_result_ts1755007796886);
                    end else begin
                        next_dtl_result_ts1755007796886 = inj_dtl_result_reg_1755007796886_763;
                    end
                    inj_dtl_result_reg_1755007796886_763 <= next_dtl_result_ts1755007796886;
                end
            end
            // END: deep_task_logic_ts1755007796886

        always @(posedge clk) begin
        if (internal_reg_ts1755007796885) begin
            reg_data_ts1755007796885 <= inj_in_a_1755007796885_345;
        end
        end
        assign inj_data_out_1755007796885_730 = reg_data_ts1755007796885;
        // END: ModClockedConditional_ts1755007796885

        // BEGIN: split_input_only_var_ts1755007796885
        always @(posedge clk) begin
            if (internal_reg_ts1755007796885) begin
                inj_data_out_k_1755007796885_826 <= inj_data_in_k_1755007796885_304;
            end
        end
        // END: split_input_only_var_ts1755007796885

    always @(posedge clk) begin 
    internal_reg_ts1755007796885 <= inj_in_a_1755007796885_345; 
    end
    assign inj_out_comb_1755007796885_253 = inj_in_a_1755007796885_345 ^ inj_in_c_1755007796885_823; 
    always @(posedge clk) begin 
    inj_out_reg_1755007796885_119 <= internal_reg_ts1755007796885 & inj_in_c_1755007796885_823; 
    end
    // END: ModClockedWithSimpleAssign_ts1755007796885

    mod_statement_block_var mod_statement_block_var_inst_1755007796885_5981 (
        .out_c(inj_out_c_1755007796885_830),
        .in_c(inj_in_c_1755007796885_823)
    );
endmodule

