module ModSimpleLogic (
    input logic a,
    input logic b,
    output logic y
);
    assign y = a ^ b;
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755007895761_651,
    input logic inj_b_1755007895761_954,
    input wire reset,
    output logic inj_y_1755007895761_324
);
    ModSimpleLogic ModSimpleLogic_inst_1755007895761_5804 (
        .a(inj_a_1755007895761_651),
        .b(inj_b_1755007895761_954),
        .y(inj_y_1755007895761_324)
    );
endmodule

