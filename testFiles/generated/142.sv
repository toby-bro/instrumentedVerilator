module ansi_implicit_inherit (
    input logic [2:0] in1,
    input logic in2,
    output logic extra_out,
    output logic out1,
    output logic out2
);
    always_comb begin
        out1 = |in1;
        out2 = |in2;
        extra_out = out1 ^ out2;
    end
endmodule

module split_case (
    input logic clk_w,
    input logic [7:0] d0_w,
    input logic [7:0] d1_w,
    input logic [7:0] d2_w,
    input logic [7:0] d3_w,
    input logic [1:0] sel_w,
    output logic [7:0] out_w
);
    always @(posedge clk_w) begin
        case (sel_w)
            2'b00: out_w <= d0_w;
            2'b01: out_w <= d1_w;
            2'b10: out_w <= d2_w;
            default: out_w <= d3_w;
        endcase
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_d0_w_1755007800508_799,
    input logic [7:0] inj_d1_w_1755007800508_120,
    input logic [7:0] inj_d2_w_1755007800508_548,
    input logic [7:0] inj_d3_w_1755007800508_354,
    input logic [2:0] inj_in1_1755007800508_882,
    input logic inj_in2_1755007800508_703,
    input logic [1:0] inj_sel_w_1755007800508_649,
    input wire reset,
    output logic inj_extra_out_1755007800508_829,
    output logic inj_out1_1755007800508_565,
    output logic inj_out2_1755007800508_253,
    output logic [7:0] inj_out_w_1755007800508_526
);
    ansi_implicit_inherit ansi_implicit_inherit_inst_1755007800508_2063 (
        .extra_out(inj_extra_out_1755007800508_829),
        .out1(inj_out1_1755007800508_565),
        .out2(inj_out2_1755007800508_253),
        .in1(inj_in1_1755007800508_882),
        .in2(inj_in2_1755007800508_703)
    );
    split_case split_case_inst_1755007800508_9071 (
        .clk_w(clk),
        .d0_w(inj_d0_w_1755007800508_799),
        .d1_w(inj_d1_w_1755007800508_120),
        .d2_w(inj_d2_w_1755007800508_548),
        .d3_w(inj_d3_w_1755007800508_354),
        .sel_w(inj_sel_w_1755007800508_649),
        .out_w(inj_out_w_1755007800508_526)
    );
endmodule

