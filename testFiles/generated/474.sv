module arith_comp_ops (
    input logic [15:0] in1,
    input logic [15:0] in2,
    input logic [15:0] in3,
    input logic [15:0] in4,
    input logic [15:0] in5,
    output logic out
);
    assign out = (in1 + in2) * in3 > in4 - in5;
endmodule

module snippet (
    input wire clk,
    input logic [15:0] inj_in1_1755007912656_127,
    input logic [15:0] inj_in2_1755007912656_198,
    input logic [15:0] inj_in3_1755007912656_868,
    input logic [15:0] inj_in4_1755007912656_568,
    input logic [15:0] inj_in5_1755007912656_631,
    input wire reset,
    output logic inj_out_1755007912656_832
);
    arith_comp_ops arith_comp_ops_inst_1755007912656_8303 (
        .in4(inj_in4_1755007912656_568),
        .in5(inj_in5_1755007912656_631),
        .out(inj_out_1755007912656_832),
        .in1(inj_in1_1755007912656_127),
        .in2(inj_in2_1755007912656_198),
        .in3(inj_in3_1755007912656_868)
    );
endmodule

