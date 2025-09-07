module snippet (
    input wire clk,
    input logic inj_bind_in_1755007905578_685,
    input bit [7:0] inj_in1_1755007905578_888,
    input bit [7:0] inj_in2_1755007905578_537,
    input wire reset,
    output logic inj_bind_out_1755007905578_433,
    output bit [7:0] inj_out1_1755007905578_713,
    output bit [7:0] inj_out2_1755007905578_356
);
    // BEGIN: bind_module_ts1755007905578
    // BEGIN: comb_simple_ts1755007905578
    always @* begin
        inj_out1_1755007905578_713 = inj_in1_1755007905578_888 & inj_in2_1755007905578_537;
        inj_out2_1755007905578_356 = inj_in1_1755007905578_888 | inj_in2_1755007905578_537;
    end
    // END: comb_simple_ts1755007905578

    assign inj_bind_out_1755007905578_433 = inj_bind_in_1755007905578_685;
    // END: bind_module_ts1755007905578
endmodule

