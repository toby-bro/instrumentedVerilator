module Seq_DFF (
    input wire clk,
    input wire [7:0] d_in,
    input wire rst,
    output reg [7:0] q_out
);
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            q_out <= 8'b0;
        end else begin
            q_out <= d_in;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_a_1755007841113_362,
    input logic [3:0] inj_b_1755007841113_225,
    input logic inj_condition_p_1755007841112_115,
    input wire [7:0] inj_d_in_1755007841112_719,
    input logic [15:0] inj_data0_1755007841114_261,
    input logic [15:0] inj_data1_1755007841114_445,
    input logic [7:0] inj_in_val_p_1755007841112_41,
    input wire reset,
    output logic [7:0] inj_data_out_1755007841113_342,
    output logic [15:0] inj_data_out_1755007841114_115,
    output logic inj_out1_bind_def_1755007841113_283,
    output logic [7:0] inj_out_reg_p_1755007841112_193,
    output logic inj_out_valid_1755007841115_795,
    output reg [7:0] inj_q_out_1755007841112_648,
    output logic [3:0] inj_sum_1755007841113_65
);
    // BEGIN: split_if_empty_then_ts1755007841113
    // BEGIN: CombinationalLogicImplicit_ts1755007841113
    // BEGIN: mod_basic_bind_ts1755007841113
    // BEGIN: sequential_register_en_ts1755007841114
    // BEGIN: CombinationalLogicExplicit_ts1755007841114
    // BEGIN: ModuleImplicitPort_ts1755007841115
    logic valid_ts1755007841115;
    assign valid_ts1755007841115 = |inj_in_val_p_1755007841112_41;
    assign inj_out_valid_1755007841115_795 = valid_ts1755007841115;
    // END: ModuleImplicitPort_ts1755007841115

    always @(inj_condition_p_1755007841112_115 or inj_data0_1755007841114_261 or inj_data1_1755007841114_445) begin
        if (inj_condition_p_1755007841112_115) begin
            inj_data_out_1755007841114_115 = inj_data1_1755007841114_445;
        end else begin
            inj_data_out_1755007841114_115 = inj_data0_1755007841114_261;
        end
    end
    // END: CombinationalLogicExplicit_ts1755007841114

    always_ff @(posedge clk) begin
        if (inj_condition_p_1755007841112_115) begin
            inj_data_out_1755007841113_342 <= inj_in_val_p_1755007841112_41;
        end
    end
    // END: sequential_register_en_ts1755007841114

    assign inj_out1_bind_def_1755007841113_283 = ~inj_condition_p_1755007841112_115;
    // END: mod_basic_bind_ts1755007841113

    always @* begin
        inj_sum_1755007841113_65 = inj_a_1755007841113_362 + inj_b_1755007841113_225;
    end
    // END: CombinationalLogicImplicit_ts1755007841113

    always @(posedge clk) begin
        if (inj_condition_p_1755007841112_115) begin
        end else begin
            inj_out_reg_p_1755007841112_193 <= inj_in_val_p_1755007841112_41;
        end
    end
    // END: split_if_empty_then_ts1755007841113

    Seq_DFF Seq_DFF_inst_1755007841112_4809 (
        .rst(reset),
        .q_out(inj_q_out_1755007841112_648),
        .clk(clk),
        .d_in(inj_d_in_1755007841112_719)
    );
endmodule

