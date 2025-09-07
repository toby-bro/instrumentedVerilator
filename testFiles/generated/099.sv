module wide_bus_ops (
    input wire [63:0] wide_a,
    input wire [63:0] wide_b,
    output wire [127:0] concat_out,
    output wire [7:0] reduce_xor_out,
    output wire [63:0] wide_sum
);
    assign wide_sum = wide_a + wide_b;
    assign reduce_xor_out = ^wide_a[63:0];
    assign concat_out = {wide_a, wide_b};
endmodule

module snippet (
    input wire clk,
    input wire [63:0] inj_wide_a_1755007785691_477,
    input wire [63:0] inj_wide_b_1755007785691_789,
    input wire reset,
    output wire [127:0] inj_concat_out_1755007785691_361,
    output wire [7:0] inj_reduce_xor_out_1755007785691_738,
    output wire [63:0] inj_wide_sum_1755007785691_753
);
    wide_bus_ops wide_bus_ops_inst_1755007785691_8767 (
        .wide_a(inj_wide_a_1755007785691_477),
        .wide_b(inj_wide_b_1755007785691_789),
        .concat_out(inj_concat_out_1755007785691_361),
        .reduce_xor_out(inj_reduce_xor_out_1755007785691_738),
        .wide_sum(inj_wide_sum_1755007785691_753)
    );
endmodule

