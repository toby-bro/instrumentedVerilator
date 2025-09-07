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
    input logic inj_data0_1755007755284_130,
    input logic inj_data1_1755007755284_26,
    input logic inj_sel_1755007755284_656,
    input wire reset,
    output logic inj_result_1755007755284_554
);
    multiplexer_2to1 multiplexer_2to1_inst_1755007755284_4559 (
        .data1(inj_data1_1755007755284_26),
        .sel(inj_sel_1755007755284_656),
        .result(inj_result_1755007755284_554),
        .data0(inj_data0_1755007755284_130)
    );
endmodule

