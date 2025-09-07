module snippet (
    input wire clk,
    input wire [1:0] inj_dtl_action_sel_1755007875488_466,
    input wire [7:0] inj_dtl_data_a_1755007875488_247,
    input wire [7:0] inj_dtl_data_b_1755007875488_391,
    input logic inj_in_j_1755007875488_446,
    input logic inj_in_k_1755007875488_157,
    input wire reset,
    output logic [7:0] inj_dtl_result_reg_1755007875488_396,
    output logic inj_out_l_1755007875488_349
);
    // BEGIN: LintLatch_ts1755007875488
    // BEGIN: deep_task_logic_ts1755007875490
    task automatic perform_action;
        input [7:0] in_a;
        input [7:0] in_b;
        input [1:0] action;
        output logic [7:0] calculated_res_ts1755007875489;
        logic [7:0] temp_task_calc_ts1755007875489;
        if (action[0]) begin
            if (action[1]) begin
                temp_task_calc_ts1755007875489 = in_a + in_b;
            end else begin
                temp_task_calc_ts1755007875489 = in_a - in_b;
            end
        end else begin
            if (action[1]) begin
                temp_task_calc_ts1755007875489 = in_a & in_b;
            end else begin
                temp_task_calc_ts1755007875489 = in_a | in_b;
            end
        end
        case (temp_task_calc_ts1755007875489[1:0])
            2'b00: calculated_res_ts1755007875489 = temp_task_calc_ts1755007875489 ^ 8'hFF;
            2'b01: calculated_res_ts1755007875489 = temp_task_calc_ts1755007875489 + 1;
            2'b10: calculated_res_ts1755007875489 = temp_task_calc_ts1755007875489 - 1;
            default: calculated_res_ts1755007875489 = temp_task_calc_ts1755007875489;
        endcase
    endtask
    always_ff @(posedge clk or negedge reset) begin
        if (!reset) begin
            inj_dtl_result_reg_1755007875488_396 <= 8'd0;
        end else begin
            logic [7:0] next_dtl_result_ts1755007875489;
            if (clk) begin
                perform_action(inj_dtl_data_a_1755007875488_247, inj_dtl_data_b_1755007875488_391, inj_dtl_action_sel_1755007875488_466, next_dtl_result_ts1755007875489);
            end else begin
                next_dtl_result_ts1755007875489 = inj_dtl_result_reg_1755007875488_396;
            end
            inj_dtl_result_reg_1755007875488_396 <= next_dtl_result_ts1755007875489;
        end
    end
    // END: deep_task_logic_ts1755007875490

    always_comb begin
        if (inj_in_j_1755007875488_446) begin
            inj_out_l_1755007875488_349 = inj_in_k_1755007875488_157;
        end else begin
            inj_out_l_1755007875488_349 = 1'b0; 
        end
    end
    // END: LintLatch_ts1755007875488
endmodule

