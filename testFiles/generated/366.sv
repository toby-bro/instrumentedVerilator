module snippet (
    input wire clk,
    input logic inj_d_1755007877224_49,
    input wire reset,
    output logic inj_q_1755007877224_688
);
    // BEGIN: ModClockedResetReg_ts1755007877224
    always @(posedge clk or negedge reset) begin
    if (!reset) begin
        inj_q_1755007877224_688 <= 1'b0;
    end else begin
        inj_q_1755007877224_688 <= inj_d_1755007877224_49;
    end
    end
    // END: ModClockedResetReg_ts1755007877224
endmodule

