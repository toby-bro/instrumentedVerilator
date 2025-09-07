module snippet (
    input wire clk,
    input logic [15:0] inj_data_in_1755007765899_136,
    input logic [7:0] inj_in1_a_1755007765900_134,
    input wire reset,
    output logic [15:0] inj_data_out_1755007765899_22,
    output logic [7:0] inj_out1_a_1755007765900_119
);
    // BEGIN: SequentialLogicPlaceholder_ts1755007765900
    // BEGIN: split_basic_blocking_ts1755007765900
    always @(*) begin
        inj_out1_a_1755007765900_119 = inj_in1_a_1755007765900_134;
    end
    // END: split_basic_blocking_ts1755007765900

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            inj_data_out_1755007765899_22 <= 16'h0;
        end else begin
            inj_data_out_1755007765899_22 <= inj_data_in_1755007765899_136;
        end
    end
    // END: SequentialLogicPlaceholder_ts1755007765900
endmodule

