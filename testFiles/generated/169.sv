module snippet (
    input wire clk,
    input wire [31:0] inj_wide_in_1755007809774_542,
    input wire reset,
    output wire [7:0] inj_lower_byte_out_1755007809774_556,
    output wire [7:0] inj_upper_byte_out_1755007809774_111
);
    // BEGIN: part_select_ops_ts1755007809774
    wire [31:0] processed_wide_ts1755007809774;
    assign processed_wide_ts1755007809774 = inj_wide_in_1755007809774_542 * 2;
    assign inj_upper_byte_out_1755007809774_111 = processed_wide_ts1755007809774[31:24];
    assign inj_lower_byte_out_1755007809774_556 = processed_wide_ts1755007809774[7:0];
    // END: part_select_ops_ts1755007809774
endmodule

