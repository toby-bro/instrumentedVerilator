module ModClockedConditional (
    input logic clk,
    input logic data_in,
    input logic enable,
    output logic data_out
);
    logic reg_data;
    always @(posedge clk) begin
    if (enable) begin
        reg_data <= data_in;
    end
    end
    assign data_out = reg_data;
endmodule

module split_seq_dependency (
    input logic clk_c,
    input logic [7:0] in_val_c,
    output logic [7:0] out_val_c
);
    logic [7:0] mid_val_c;
    always @(posedge clk_c) begin
        mid_val_c <= in_val_c + 1;
        out_val_c <= mid_val_c * 2;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_data_in_1755007819293_881,
    input logic inj_enable_1755007819293_447,
    input logic [7:0] inj_in_val_c_1755007819293_114,
    input wire reset,
    output logic inj_data_out_1755007819293_888,
    output logic [7:0] inj_out_val_c_1755007819293_633
);
    split_seq_dependency split_seq_dependency_inst_1755007819293_3367 (
        .in_val_c(inj_in_val_c_1755007819293_114),
        .out_val_c(inj_out_val_c_1755007819293_633),
        .clk_c(clk)
    );
    ModClockedConditional ModClockedConditional_inst_1755007819293_4085 (
        .enable(inj_enable_1755007819293_447),
        .data_out(inj_data_out_1755007819293_888),
        .clk(clk),
        .data_in(inj_data_in_1755007819293_881)
    );
endmodule

