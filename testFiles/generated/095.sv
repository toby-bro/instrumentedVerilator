module always_comb_if (
    input logic cond,
    input logic [31:0] in1,
    input logic [31:0] in2,
    output logic [31:0] out
);
    always_comb begin
        if (cond) begin
            out = in1;
        end else begin
            out = in2;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_cond_1755007784267_296,
    input logic [31:0] inj_in1_1755007784267_174,
    input logic [31:0] inj_in2_1755007784267_343,
    input wire reset,
    output logic [31:0] inj_out_1755007784267_506
);
    always_comb_if always_comb_if_inst_1755007784267_3141 (
        .cond(inj_cond_1755007784267_296),
        .in1(inj_in1_1755007784267_174),
        .in2(inj_in2_1755007784267_343),
        .out(inj_out_1755007784267_506)
    );
endmodule

