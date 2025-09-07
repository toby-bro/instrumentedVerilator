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

module simple_assign (
    input logic [7:0] in,
    output logic [7:0] out
);
    assign out = in;
endmodule

module snippet (
    input wire clk,
    input logic inj_condition_e_1755007884329_147,
    input logic [3:0] inj_i_bind_control_1755007884332_378,
    input logic [1:0] inj_in_val_1755007884328_171,
    input logic [7:0] inj_in_val_c_1755007884328_199,
    input wire [15:0] inj_value1_1755007884327_399,
    input wire [15:0] inj_value2_1755007884327_790,
    input wire reset,
    output logic inj_o_bind_status_1755007884332_424,
    output logic [7:0] inj_out_1755007884331_369,
    output logic [7:0] inj_out_q_1755007884328_356,
    output logic [7:0] inj_out_reg_t_1755007884330_827,
    output reg inj_out_res_1755007884328_0,
    output logic [7:0] inj_out_val_c_1755007884328_580,
    output logic [7:0] inj_out_val_e_1755007884329_402,
    output reg [15:0] inj_result_val_1755007884327_915,
    output logic inj_status_e_1755007884329_992
);
    // BEGIN: Comb_IfElse_ts1755007884328
    // BEGIN: split_seq_dependency_ts1755007884328
    logic [7:0] mid_val_c_ts1755007884328;
        // BEGIN: split_mixed_cond_seq_ts1755007884329
        logic [7:0] temp_val_e_ts1755007884329;
            // BEGIN: module_to_bind_ts1755007884332
            always_comb inj_o_bind_status_1755007884332_424 = |inj_i_bind_control_1755007884332_378;
            // END: module_to_bind_ts1755007884332

            simple_assign simple_assign_inst_1755007884331_2659 (
                .out(inj_out_1755007884331_369),
                .in(inj_in_val_c_1755007884328_199)
            );
            // BEGIN: split_if_empty_branches_ts1755007884330
            always @(posedge clk) begin
                if (inj_condition_e_1755007884329_147) begin
                end else begin
                end
            end
            // END: split_if_empty_branches_ts1755007884330

        always @(posedge clk) begin
            temp_val_e_ts1755007884329 <= mid_val_c_ts1755007884328 + 5;
            if (inj_condition_e_1755007884329_147) begin
                inj_out_val_e_1755007884329_402 <= temp_val_e_ts1755007884329;
                inj_status_e_1755007884329_992 <= 1;
            end else begin
                inj_out_val_e_1755007884329_402 <= inj_in_val_c_1755007884328_199;
                inj_status_e_1755007884329_992 <= 0;
            end
        end
        // END: split_mixed_cond_seq_ts1755007884329

        // BEGIN: split_single_stmt_ts1755007884328
        always @(*) begin
            inj_out_q_1755007884328_356 = inj_in_val_c_1755007884328_199 + 1;
        end
        // END: split_single_stmt_ts1755007884328

    always @(posedge clk) begin
        mid_val_c_ts1755007884328 <= inj_in_val_c_1755007884328_199 + 1;
        inj_out_val_c_1755007884328_580 <= mid_val_c_ts1755007884328 * 2;
    end
    // END: split_seq_dependency_ts1755007884328

    case_single_default_after_item case_single_default_after_item_inst_1755007884328_5441 (
        .in_val(inj_in_val_1755007884328_171),
        .out_res(inj_out_res_1755007884328_0)
    );
    always_comb begin
        if (reset) begin
            inj_result_val_1755007884327_915 = inj_value1_1755007884327_399;
        end else begin
            inj_result_val_1755007884327_915 = inj_value2_1755007884327_790;
        end
    end
    // END: Comb_IfElse_ts1755007884328
endmodule

