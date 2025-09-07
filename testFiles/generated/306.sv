module multi_always_comb (
    input wire [7:0] in1,
    input wire [7:0] in2,
    output wire [7:0] out1,
    output wire [7:0] out2
);
    logic [7:0] intermediate1;
    logic [7:0] intermediate2;
    always @(*) begin
        intermediate1 = in1 & in2;
    end
    always @(*) begin
        intermediate2 = in1 | in2;
    end
    assign out1 = intermediate1 + 8'd1;
    assign out2 = intermediate2 - 8'd1;
endmodule

module snippet (
    input wire clk,
    input wire [7:0] inj_in1_1755007857463_746,
    input wire [7:0] inj_in2_1755007857463_399,
    input wire reset,
    output wire [7:0] inj_out1_1755007857463_860,
    output wire [7:0] inj_out2_1755007857463_256
);
    multi_always_comb multi_always_comb_inst_1755007857463_9893 (
        .out1(inj_out1_1755007857463_860),
        .out2(inj_out2_1755007857463_256),
        .in1(inj_in1_1755007857463_746),
        .in2(inj_in2_1755007857463_399)
    );
endmodule

