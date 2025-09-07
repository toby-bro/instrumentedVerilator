module snippet (
    input wire clk,
    input logic inj_condition_o_1755007818601_723,
    input logic [7:0] inj_in_false_o_1755007818601_128,
    input logic [7:0] inj_in_true_o_1755007818601_986,
    input wire reset,
    output logic [7:0] inj_out_val_o_1755007818601_137
);
    // BEGIN: split_conditional_blocking_ts1755007818601
    always @(*) begin
        if (inj_condition_o_1755007818601_723) begin
            inj_out_val_o_1755007818601_137 = inj_in_true_o_1755007818601_986;
        end else begin
            inj_out_val_o_1755007818601_137 = inj_in_false_o_1755007818601_128;
        end
    end
    // END: split_conditional_blocking_ts1755007818601
endmodule

