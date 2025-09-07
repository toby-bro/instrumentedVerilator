module snippet (
    input wire clk,
    input wire [63:0] inj_wide_a_1755007897780_971,
    input wire [63:0] inj_wide_b_1755007897780_971,
    input wire reset,
    output wire [127:0] inj_concat_out_1755007897780_43,
    output wire [7:0] inj_reduce_xor_out_1755007897780_816,
    output wire [63:0] inj_wide_sum_1755007897780_262
);
    // BEGIN: wide_bus_ops_ts1755007897780
    assign inj_wide_sum_1755007897780_262 = inj_wide_a_1755007897780_971 + inj_wide_b_1755007897780_971;
    assign inj_reduce_xor_out_1755007897780_816 = ^inj_wide_a_1755007897780_971[63:0];
    assign inj_concat_out_1755007897780_43 = {inj_wide_a_1755007897780_971, inj_wide_b_1755007897780_971};
    // END: wide_bus_ops_ts1755007897780
endmodule

