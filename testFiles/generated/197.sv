module snippet (
    input wire clk,
    input logic inj_data0_1755007818967_632,
    input logic inj_data1_1755007818967_387,
    input logic inj_sel_1755007818967_454,
    input wire reset,
    output logic inj_result_1755007818967_480
);
    // BEGIN: multiplexer_2to1_ts1755007818967
    assign inj_result_1755007818967_480 = inj_sel_1755007818967_454 ? inj_data1_1755007818967_387 : inj_data0_1755007818967_632;
    // END: multiplexer_2to1_ts1755007818967
endmodule

