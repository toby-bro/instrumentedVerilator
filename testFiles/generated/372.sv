module snippet (
    input wire clk,
    input logic inj_d_1755007879013_327,
    input wire reset,
    output logic inj_q_1755007879013_488
);
    // BEGIN: ModClockedResetReg_ts1755007879013
    always @(posedge clk or negedge reset) begin
    if (!reset) begin
        inj_q_1755007879013_488 <= 1'b0;
    end else begin
        inj_q_1755007879013_488 <= inj_d_1755007879013_327;
    end
    end
    // END: ModClockedResetReg_ts1755007879013
endmodule

