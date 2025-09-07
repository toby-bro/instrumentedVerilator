module snippet (
    input wire clk,
    input logic [15:0] inj_in1_1755007818322_884,
    input logic [15:0] inj_in2_1755007818322_852,
    input logic [15:0] inj_in3_1755007818322_658,
    input logic [15:0] inj_in4_1755007818322_336,
    input logic [15:0] inj_in5_1755007818322_388,
    input wire reset,
    output logic inj_out_1755007818322_602
);
    // BEGIN: arith_comp_ops_ts1755007818323
    assign inj_out_1755007818322_602 = (inj_in1_1755007818322_884 + inj_in2_1755007818322_852) * inj_in3_1755007818322_658 > inj_in4_1755007818322_336 - inj_in5_1755007818322_388;
    // END: arith_comp_ops_ts1755007818323
endmodule

