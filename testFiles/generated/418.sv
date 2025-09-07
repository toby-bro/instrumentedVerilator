module ConcatVectorOps (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [7:0] c,
    output logic [15:0] out_concat
);
    assign out_concat = {a, b, c};
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_a_1755007894123_682,
    input logic [3:0] inj_b_1755007894123_187,
    input logic [7:0] inj_c_1755007894123_222,
    input wire reset,
    output logic [15:0] inj_out_concat_1755007894123_692
);
    ConcatVectorOps ConcatVectorOps_inst_1755007894123_2360 (
        .a(inj_a_1755007894123_682),
        .b(inj_b_1755007894123_187),
        .c(inj_c_1755007894123_222),
        .out_concat(inj_out_concat_1755007894123_692)
    );
endmodule

