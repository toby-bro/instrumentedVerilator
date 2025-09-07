module BitwiseOps(
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [3:0] o_and,
    output logic [3:0] o_or,
    output logic [3:0] o_xor,
    output logic [3:0] o_not
);
    assign o_and = a & b;
    assign o_or  = a | b;
    assign o_xor = a ^ b;
    assign o_not = ~a;
endmodule
module ReductionOps(
    input  logic [7:0] data,
    output logic       red_and,
    output logic       red_or,
    output logic       red_xor
);
    assign red_and = &data;
    assign red_or  = |data;
    assign red_xor = ^data;
endmodule
module ShiftOps(
    input  logic [7:0]           data,
    input  logic signed [7:0]    sdata,
    input  logic [2:0]           shamt,
    output logic [7:0]           out_lsl,
    output logic [7:0]           out_lsr,
    output logic signed [7:0]    out_asr
);
    assign out_lsl = data << shamt;
    assign out_lsr = data >> shamt;
    assign out_asr = sdata >>> shamt;
endmodule
module BitSelect(
    input  logic [7:0] a,
    output logic       bit0,
    output logic [2:0] high3
);
    assign bit0  = a[0];
    assign high3 = a[7:5];
endmodule
module ConcatReplicate(
    input  logic [1:0] a,
    output logic [3:0] concat_out,
    output logic [3:0] rep2_out
);
    assign concat_out = {a, a};
    assign rep2_out   = {2{a}}; 
endmodule
module ConditionalOp(
    input  logic [3:0] a,
    input  logic [3:0] b,
    input  logic       sel,
    output logic [3:0] out
);
    assign out = sel ? a : b;
endmodule
module ArithOps(
    input  logic signed [7:0] a,
    input  logic signed [7:0] b,
    output logic signed [7:0] sum,
    output logic signed [7:0] diff,
    output logic signed [7:0] prod,
    output logic signed [7:0] quot,
    output logic signed [7:0] remd
);
    assign sum  = a + b;
    assign diff = a - b;
    assign prod = a * b;
    assign quot = a / b;
    assign remd = a % b;
endmodule
module CompareOps(
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic       eq,
    output logic       neq,
    output logic       lt,
    output logic       lte,
    output logic       gt,
    output logic       gte
);
    assign eq  = (a == b);
    assign neq = (a != b);
    assign lt  = (a <  b);
    assign lte = (a <= b);
    assign gt  = (a >  b);
    assign gte = (a >= b);
endmodule
module PowerOfTwo(
    input  logic [7:0]            val,
    output logic                  is_pow2,
    output logic [3:0]            ctz,
    output logic [3:0]            msb_pos
);
    assign is_pow2 = (val != 0) & ((val & (val - 1)) == 0);
    always_comb begin
        if      (val[0]) ctz = 0;
        else if (val[1]) ctz = 1;
        else if (val[2]) ctz = 2;
        else if (val[3]) ctz = 3;
        else if (val[4]) ctz = 4;
        else if (val[5]) ctz = 5;
        else if (val[6]) ctz = 6;
        else if (val[7]) ctz = 7;
        else             ctz = 8;
    end
    always_comb begin
        if      (val[7]) msb_pos = 7;
        else if (val[6]) msb_pos = 6;
        else if (val[5]) msb_pos = 5;
        else if (val[4]) msb_pos = 4;
        else if (val[3]) msb_pos = 3;
        else if (val[2]) msb_pos = 2;
        else if (val[1]) msb_pos = 1;
        else if (val[0]) msb_pos = 0;
        else             msb_pos = 8;
    end
endmodule
module ComplexTree(
    input  logic [7:0]           a,
    input  logic [7:0]           b,
    input  logic [7:0]           c,
    input  logic [2:0]           sh,
    output logic [7:0]           out
);
    logic [7:0] t1;
    logic       flag;
    assign t1   = ((a & b) ^ (~c)) << sh;
    assign flag = (&{a[0], b[0]}) | |{c[3], c[2]};
    assign out  = (t1 & {2{b[7:6]}}) | (flag ? {4{1'b1}} : {4'b1010});
endmodule
module NestedRepConcat(
    input  logic [2:0] x,
    output logic [7:0] nested_concat,
    output logic [5:0] nested_rep
);
    assign nested_concat = {{{x[2:1]}, {x[0]}}, {2{x[1]}}};
    assign nested_rep    = {3{{2{x[0]}}}}[5:0];
endmodule
module SignedCondition(
    input  logic signed [4:0] p,
    input  logic signed [4:0] q,
    input  logic              sel,
    output logic signed [4:0] z
);
    assign z = (p > q) ? p : (sel ? q : -p);
endmodule
module ArithmeticTree(
    input  logic [3:0] u,
    input  logic [3:0] v,
    output logic [4:0] sum_tree,
    output logic [4:0] diff_tree
);
    logic [4:0] t0;
    assign t0        = u + v;
    assign sum_tree  = (t0 & 5'b11111) + 1;
    assign diff_tree = ((t0 ^ 5'b01010) - 5'd3) & 5'b01111;
endmodule
module ReplicateSelect(
    input  logic [1:0] a,
    output logic [1:0] sel_out,
    output logic [3:0] rep_out
);
    assign rep_out  = {4{a}};
    assign sel_out  = rep_out[2:1];
endmodule
module ZeroFold(
    input logic enable,
    input logic [3:0] d,
    output logic [3:0] o
);
    assign o = enable ? (d << 1) : 4'b0000;
endmodule
module BlendOps(
    input  logic [3:0] A,
    input  logic [3:0] B,
    input  logic [3:0] M,
    output logic [3:0] blended
);
    assign blended = (M & A) | (~M & B);
endmodule
