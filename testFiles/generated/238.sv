module snippet (
    input wire clk,
    input logic [7:0] inj_i1_r_1755007833799_574,
    input logic [7:0] inj_i2_r_1755007833799_383,
    input logic [7:0] inj_i3_r_1755007833799_86,
    input wire reset,
    output logic [7:0] inj_o1_r_1755007833799_151,
    output logic [7:0] inj_o2_r_1755007833799_732,
    output logic [7:0] inj_o3_r_1755007833799_16
);
    // BEGIN: split_complex_blocking_ts1755007833799
    logic [7:0] t1_r_ts1755007833799, t2_r_ts1755007833799;
    always @(*) begin
        t1_r_ts1755007833799 = inj_i1_r_1755007833799_574 + inj_i2_r_1755007833799_383;
        inj_o1_r_1755007833799_151 = t1_r_ts1755007833799 - inj_i3_r_1755007833799_86;
        t2_r_ts1755007833799 = inj_i2_r_1755007833799_383 * inj_i3_r_1755007833799_86;
        inj_o2_r_1755007833799_732 = t1_r_ts1755007833799 + t2_r_ts1755007833799;
        inj_o3_r_1755007833799_16 = t2_r_ts1755007833799 / 2;
    end
    // END: split_complex_blocking_ts1755007833799
endmodule

