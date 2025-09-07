module slice_variable(input  logic [63:0] data, input  logic [5:0] idx, output logic [7:0] out);
  assign out = data[idx*8 +: 8];
endmodule
module replicate8to32(input  logic [7:0] a, output logic [31:0] out);
  assign out = {4{a}};
endmodule
module concat16to32(input  logic [15:0] a, input  logic [15:0] b, output logic [31:0] out);
  assign out = {a, b};
endmodule
module reductions64(input  logic [63:0] a, output logic and_red, output logic or_red, output logic xor_red);
  assign and_red = &a;
  assign or_red  = |a;
  assign xor_red = ^a;
endmodule
module bitwise_ops(input  logic [31:0] a, input  logic [31:0] b,
                   output logic [31:0] c_and, output logic [31:0] c_or,
                   output logic [31:0] c_xor, output logic [31:0] c_not);
  assign c_and = a & b;
  assign c_or  = a | b;
  assign c_xor = a ^ b;
  assign c_not = ~a;
endmodule
module arith16(input  logic signed [15:0] a, input  logic signed [15:0] b,
               output logic signed [15:0] sum, output logic signed [15:0] diff);
  assign sum  = a + b;
  assign diff = a - b;
endmodule
module shift_var(input  logic [15:0] a, input  logic [4:0] sh,
                 output logic [15:0] sl, output logic [15:0] sr);
  assign sl = a << sh;
  assign sr = a >> sh;
endmodule
module ternary8(input  logic sel, input  logic [7:0] a, input  logic [7:0] b,
                output logic [7:0] y);
  assign y = sel ? a : b;
endmodule
module wide_slice(input  logic [95:0] wide, input  logic [5:0] idx, output logic [7:0] outp);
  assign outp = (wide >> idx) & 8'hFF;
endmodule
module cast_signed(input  logic signed [7:0] a, output logic [15:0] b);
  assign b = {8'b0, a};
endmodule
module array_select(input  logic [7:0] arr [0:3], input  logic [1:0] idx,
                    output logic [7:0] element);
  assign element = arr[idx];
endmodule
module bit_slice_const(input  logic [31:0] a, output logic [7:0] b);
  assign b = a[15:8];
endmodule
module eq_neq(input  logic [31:0] a, input  logic [31:0] b,
              output logic eq, output logic neq);
  assign eq  = (a == b);
  assign neq = (a != b);
endmodule
module nested_concat_rep(input  logic [3:0] a, input  logic [3:0] b, output logic [31:0] out);
  assign out = {{2{a}}, {b, a}};
endmodule
