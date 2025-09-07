module ConcatRepl(input logic [3:0] in, output logic [7:0] out1, output logic [1:0] out2);
  assign out1 = {in, in};
  assign out2 = {2{in[0]}};
endmodule
module ReductionOps(input logic [7:0] a, output logic andr, output logic orr, output logic xorr);
  assign andr = &a;
  assign orr  = |a;
  assign xorr = ^a;
endmodule
module ShiftOps(input logic [7:0] a, input logic [2:0] sh, output logic [7:0] lshift, output logic [7:0] rshift, output logic [7:0] arith_shift);
  assign lshift     = a << sh;
  assign rshift     = a >> sh;
  assign arith_shift = $signed(a) >>> sh;
endmodule
module PartSelect(input logic [15:0] a, input logic [3:0] msb, input logic [3:0] lsb, output logic [7:0] slice1, output logic [7:0] slice2);
  assign slice1 = a[msb -: 8];
  assign slice2 = a[lsb +: 8];
endmodule
module ConditionalOp(input logic en, input logic [3:0] a, output logic [3:0] y);
  assign y = en ? (a + 1) : (a - 1);
endmodule
module RealConv(input real x, output logic [63:0] bits);
  assign bits = $realtobits(x);
endmodule
module BitsToReal(input logic [63:0] bits, output real y);
  assign y = $bitstoreal(bits);
endmodule
module StringOps(input  string in, output string out);
  always_comb begin
    string s;
    s = in;
    out = {s, "end"};
  end
endmodule
module DynBitSelect(input logic [15:0] a, input logic [3:0] idx, output logic bit_val);
  assign bit_val = a[idx];
endmodule
module StreamConcat(input logic [3:0] a, input logic [3:0] b, output logic [7:0] out);
  assign out = {<<{a, b}};
endmodule
module ArithmeticOps(input logic [7:0] a, input logic [7:0] b,
                     output logic [8:0] sum, output logic [7:0] diff,
                     output logic [15:0] prod, output logic [7:0] quot);
  assign sum  = a + b;
  assign diff = a - b;
  assign prod = a * b;
  assign quot = a / b;
endmodule
module LogicalOps(input logic [3:0] a, input logic [3:0] b,
                  output logic [3:0] and_out, output logic [3:0] or_out,
                  output logic [3:0] xor_out, output logic [3:0] not_out);
  assign and_out = a & b;
  assign or_out  = a | b;
  assign xor_out = a ^ b;
  assign not_out = ~a;
endmodule
module EqualityOps(input logic [3:0] a, input logic [3:0] b,
                   output logic eq, output logic neq,
                   output logic case_eq, output logic case_neq,
                   output logic inside_eq);
  assign eq        = (a == b);
  assign neq       = (a != b);
  assign case_eq   = (a === b);
  assign case_neq  = (a !== b);
  assign inside_eq = a inside {4'b0001, 4'b0010};
endmodule
module UnsizedLiteral(output logic zero, output logic one, output logic zval, output logic xval);
  assign zero = '0;
  assign one  = '1;
  assign zval = 'z;
  assign xval = 'x;
endmodule
module FourStateVector(output logic [3:0] zvec, output logic [3:0] xvec, output logic [3:0] val);
  assign zvec = 4'bzzzz;
  assign xvec = 4'bxxxx;
  assign val  = 4'b0101;
endmodule
module ArrayPort(input  logic [3:0] arr [0:3], output logic [3:0] elem);
  assign elem = arr[2];
endmodule
module SignedUnsigned(input  logic signed   [7:0] a, output logic unsigned [7:0] b);
  assign b = a;
endmodule
module ParamWidth #(parameter W = 8)(input logic [W-1:0] a, output logic [W-1:0] b);
  assign b = a;
endmodule
