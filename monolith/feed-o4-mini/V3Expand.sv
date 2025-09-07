module BitSelect(input logic [15:0] in, output logic bit0);
  assign bit0 = in[0];
endmodule
module PartSelect(input logic [31:0] in, output logic [7:0] out);
  assign out = in[15:8];
endmodule
module ConcatExample(input logic [7:0] a, input logic [7:0] b, output logic [15:0] out);
  assign out = {a, b};
endmodule
module ReplicateExample(input logic [3:0] in, output logic [15:0] out);
  assign out = {4{in}};
endmodule
module UnaryOpExample(input logic [7:0] a, output logic [7:0] nota);
  assign nota = ~a;
endmodule
module BinaryOpExample(
  input logic [7:0] a,
  input logic [7:0] b,
  output logic [7:0] and_out,
  output logic [7:0] or_out,
  output logic [7:0] xor_out
);
  assign and_out = a & b;
  assign or_out  = a | b;
  assign xor_out = a ^ b;
endmodule
module ShiftExample(
  input logic [7:0] a,
  input logic [2:0] sh,
  output logic [7:0] shr,
  output logic [7:0] shl
);
  assign shr = a >> sh;
  assign shl = a << sh;
endmodule
module CompareExample(
  input logic [7:0] a,
  input logic [7:0] b,
  output logic eq,
  output logic neq
);
  assign eq  = (a == b);
  assign neq = (a != b);
endmodule
module ReductionExample(
  input logic [7:0] a,
  output logic lor,
  output logic land,
  output logic lxor
);
  assign lor  = |a;
  assign land = &a;
  assign lxor = ^a;
endmodule
module ExtendExample(
  input logic signed [7:0] sa,
  input logic [7:0] ua,
  output logic [15:0] sext,
  output logic [15:0] zext
);
  assign sext = {{8{sa[7]}}, sa};
  assign zext = {{8{1'b0}}, ua};
endmodule
module ArraySelExample(
  input logic [3:0] arr [0:3],
  output logic bit0,
  output logic [3:0] row1
);
  assign bit0 = arr[2][1];
  assign row1 = arr[1];
endmodule
module ConditionalExample(
  input logic sel,
  input logic [7:0] a,
  input logic [7:0] b,
  output logic [7:0] out
);
  assign out = sel ? a : b;
endmodule
module CastExample(
  input logic [3:0] in,
  output logic signed [7:0] sout,
  output logic [7:0] uout
);
  assign sout = in;
  assign uout = in;
endmodule
module ClassInstExample(
  input logic clk,
  input logic [7:0] in,
  output logic [7:0] out
);
  class MyClass;
    rand logic [7:0] data;
    function logic [7:0] compute(input logic [7:0] v);
      return v + data;
    endfunction
  endclass
  always_comb begin
    MyClass obj = new();
    obj.data = in;
    out = obj.compute(in);
  end
endmodule
