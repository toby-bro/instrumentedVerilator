module multiplexer_2to1 (
    input logic data0,
    input logic data1,
    input logic sel,
    output logic result
);
    assign result = sel ? data1 : data0;
endmodule

module snippet (
    input wire clk,
    input logic inj_data0_1755007791573_11,
    input logic inj_data1_1755007791573_16,
    input logic inj_sel_1755007791573_353,
    input wire reset,
    output logic inj_result_1755007791573_847
);
    multiplexer_2to1 multiplexer_2to1_inst_1755007791573_9300 (
        .sel(inj_sel_1755007791573_353),
        .result(inj_result_1755007791573_847),
        .data0(inj_data0_1755007791573_11),
        .data1(inj_data1_1755007791573_16)
    );
endmodule

