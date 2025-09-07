module deep_task_logic (
    input wire [1:0] dtl_action_sel,
    input wire dtl_clk,
    input wire [7:0] dtl_data_a,
    input wire [7:0] dtl_data_b,
    input wire dtl_en,
    input wire dtl_rst_n,
    output logic [7:0] dtl_result_reg
);
    task automatic perform_action;
        input [7:0] in_a;
        input [7:0] in_b;
        input [1:0] action;
        output logic [7:0] calculated_res;
        logic [7:0] temp_task_calc;
        if (action[0]) begin
            if (action[1]) begin
                temp_task_calc = in_a + in_b;
            end else begin
                temp_task_calc = in_a - in_b;
            end
        end else begin
            if (action[1]) begin
                temp_task_calc = in_a & in_b;
            end else begin
                temp_task_calc = in_a | in_b;
            end
        end
        case (temp_task_calc[1:0])
            2'b00: calculated_res = temp_task_calc ^ 8'hFF;
            2'b01: calculated_res = temp_task_calc + 1;
            2'b10: calculated_res = temp_task_calc - 1;
            default: calculated_res = temp_task_calc;
        endcase
    endtask
    always_ff @(posedge dtl_clk or negedge dtl_rst_n) begin
        if (!dtl_rst_n) begin
            dtl_result_reg <= 8'd0;
        end else begin
            logic [7:0] next_dtl_result;
            if (dtl_en) begin
                perform_action(dtl_data_a, dtl_data_b, dtl_action_sel, next_dtl_result);
            end else begin
                next_dtl_result = dtl_result_reg;
            end
            dtl_result_reg <= next_dtl_result;
        end
    end
endmodule

module snippet (
    input wire clk,
    input wire [1:0] inj_dtl_action_sel_1755007834140_782,
    input wire [7:0] inj_dtl_data_a_1755007834140_299,
    input wire [7:0] inj_dtl_data_b_1755007834140_442,
    input logic [7:0] inj_in_val_1755007834140_432,
    input bit inj_trigger_input_1755007834140_190,
    input wire reset,
    output logic [7:0] inj_dtl_result_reg_1755007834140_302,
    output logic [7:0] inj_out_val_1755007834140_579,
    output bit inj_trigger_output_1755007834140_80
);
    // BEGIN: generic_class_scope_diag_mod_ts1755007834140
    // BEGIN: PragmaOnceDirective_ts1755007834140
assign inj_trigger_output_1755007834140_80 = inj_trigger_input_1755007834140_190;
    // END: PragmaOnceDirective_ts1755007834140

    assign inj_out_val_1755007834140_579 = inj_in_val_1755007834140_432;
    // END: generic_class_scope_diag_mod_ts1755007834140

    deep_task_logic deep_task_logic_inst_1755007834140_2488 (
        .dtl_data_a(inj_dtl_data_a_1755007834140_299),
        .dtl_data_b(inj_dtl_data_b_1755007834140_442),
        .dtl_en(reset),
        .dtl_rst_n(reset),
        .dtl_result_reg(inj_dtl_result_reg_1755007834140_302),
        .dtl_action_sel(inj_dtl_action_sel_1755007834140_782),
        .dtl_clk(clk)
    );
endmodule

