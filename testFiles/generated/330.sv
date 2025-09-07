module module_latch (
    input wire [7:0] in_latch_data,
    input wire in_latch_en,
    output reg [7:0] out_latch_reg
);
    always_latch begin
    if (in_latch_en) begin
        out_latch_reg = in_latch_data;
    end
    end
endmodule

module sequential_always_assign (
    input logic clk,
    input logic [7:0] in,
    output logic [7:0] out
);
    always @(posedge clk) begin
        out <= in;
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_in_1755007865137_858,
    input wire [7:0] inj_in_latch_data_1755007865137_80,
    input wire reset,
    output logic [7:0] inj_out_1755007865137_829,
    output reg [7:0] inj_out_latch_reg_1755007865137_652
);
    sequential_always_assign sequential_always_assign_inst_1755007865137_3609 (
        .clk(clk),
        .in(inj_in_1755007865137_858),
        .out(inj_out_1755007865137_829)
    );
    module_latch module_latch_inst_1755007865137_8782 (
        .in_latch_data(inj_in_latch_data_1755007865137_80),
        .in_latch_en(clk),
        .out_latch_reg(inj_out_latch_reg_1755007865137_652)
    );
endmodule

