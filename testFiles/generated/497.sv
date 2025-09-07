module Module_ControlFlow (
    input bit clk,
    input logic [7:0] data_in,
    input bit reset_n,
    input logic [2:0] sel_in,
    output reg [7:0] data_out
);
    reg [7:0] temp;
    always_comb begin
        unique case (sel_in)
            3'b000: temp = data_in;
            3'b001: temp = data_in + 1;
            3'b010: temp = data_in - 1;
            default: temp = 8'hAA;
        endcase
    end
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            data_out <= 8'h00;
        else
            data_out <= temp;
    end
endmodule

module child_scalar_port (
    input logic data_in,
    output logic data_out
);
    assign data_out = data_in;
endmodule

module snippet (
    input wire clk,
    input logic inj_control_signal_k_1755007920273_240,
    input logic [7:0] inj_data_in_k_1755007920273_274,
    input wire [1:0] inj_dtl_action_sel_1755007920275_279,
    input wire [7:0] inj_dtl_data_b_1755007920275_208,
    input wire inj_dtl_en_1755007920275_56,
    input bit inj_enable_crypto_1755007920278_838,
    input logic [2:0] inj_sel_in_1755007920273_647,
    input logic [1:0] inj_selector_1755007920274_641,
    input wire reset,
    output bit inj_crypto_active_1755007920278_584,
    output reg [7:0] inj_data_out_1755007920273_304,
    output logic inj_data_out_1755007920274_864,
    output logic [7:0] inj_data_out_k_1755007920273_280,
    output logic [7:0] inj_dtl_result_reg_1755007920275_146,
    output logic [7:0] inj_selected_output_1755007920274_977
);
    // BEGIN: split_input_only_var_ts1755007920273
    // BEGIN: generate_for_block_ts1755007920274
    wire [7:0] data_ts1755007920274 [3:0]; 
        // BEGIN: deep_task_logic_ts1755007920276
        task automatic perform_action;
            input [7:0] in_a;
            input [7:0] in_b;
            input [1:0] action;
            output logic [7:0] calculated_res_ts1755007920276;
            logic [7:0] temp_task_calc_ts1755007920276;
            if (action[0]) begin
                if (action[1]) begin
                    temp_task_calc_ts1755007920276 = in_a + in_b;
                end else begin
                    temp_task_calc_ts1755007920276 = in_a - in_b;
                end
            end else begin
                if (action[1]) begin
                    temp_task_calc_ts1755007920276 = in_a & in_b;
                end else begin
                    temp_task_calc_ts1755007920276 = in_a | in_b;
                end
            end
            case (temp_task_calc_ts1755007920276[1:0])
                2'b00: calculated_res_ts1755007920276 = temp_task_calc_ts1755007920276 ^ 8'hFF;
                2'b01: calculated_res_ts1755007920276 = temp_task_calc_ts1755007920276 + 1;
                2'b10: calculated_res_ts1755007920276 = temp_task_calc_ts1755007920276 - 1;
                default: calculated_res_ts1755007920276 = temp_task_calc_ts1755007920276;
            endcase
        endtask
        always_ff @(posedge clk or negedge reset) begin
            if (!reset) begin
                inj_dtl_result_reg_1755007920275_146 <= 8'd0;
            end else begin
                logic [7:0] next_dtl_result_ts1755007920276;
                    // BEGIN: PragmaProtectKeyBlock_ts1755007920278
                `ifdef SLANG_PRAGMA
                `protect key
                `endif
                `ifdef SLANG_PRAGMA
                `protect block
                `endif
                assign inj_crypto_active_1755007920278_584 = inj_enable_crypto_1755007920278_838;
                    // END: PragmaProtectKeyBlock_ts1755007920278

                if (inj_dtl_en_1755007920275_56) begin
                    perform_action(data_ts1755007920274, inj_dtl_data_b_1755007920275_208, inj_dtl_action_sel_1755007920275_279, next_dtl_result_ts1755007920276);
                end else begin
                    next_dtl_result_ts1755007920276 = inj_dtl_result_reg_1755007920275_146;
                end
                inj_dtl_result_reg_1755007920275_146 <= next_dtl_result_ts1755007920276;
            end
        end
        // END: deep_task_logic_ts1755007920276

    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : data_gen
            assign data_ts1755007920274[i] = 8'(i + 1) * 8'(i + 1);
        end
    endgenerate
    always_comb begin
        case (inj_selector_1755007920274_641)
            0: inj_selected_output_1755007920274_977 = data_ts1755007920274[0];
            1: inj_selected_output_1755007920274_977 = data_ts1755007920274[1];
            2: inj_selected_output_1755007920274_977 = data_ts1755007920274[2];
            3: inj_selected_output_1755007920274_977 = data_ts1755007920274[3];
            default: inj_selected_output_1755007920274_977 = 8'hXX;
        endcase
    end
    // END: generate_for_block_ts1755007920274

    child_scalar_port child_scalar_port_inst_1755007920274_5170 (
        .data_out(inj_data_out_1755007920274_864),
        .data_in(inj_control_signal_k_1755007920273_240)
    );
    Module_ControlFlow Module_ControlFlow_inst_1755007920273_3833 (
        .sel_in(inj_sel_in_1755007920273_647),
        .data_out(inj_data_out_1755007920273_304),
        .clk(clk),
        .data_in(inj_data_in_k_1755007920273_274),
        .reset_n(reset)
    );
    always @(posedge clk) begin
        if (inj_control_signal_k_1755007920273_240) begin
            inj_data_out_k_1755007920273_280 <= inj_data_in_k_1755007920273_274;
        end
    end
    // END: split_input_only_var_ts1755007920273
endmodule

