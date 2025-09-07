module and_op(input logic [3:0] a, input logic [3:0] b, output logic [3:0] out_and);
  assign out_and = a & b;
endmodule
module or_xor_op(input logic [3:0] a, input logic [3:0] b, output logic [3:0] out_or, output logic [3:0] out_xor);
  assign out_or = a | b;
  assign out_xor = a ^ b;
endmodule
module add_sub_mul_div_mod(input logic signed [7:0] a, input logic signed [7:0] b,
                           output logic signed [7:0] sum, output logic signed [7:0] diff,
                           output logic signed [15:0] prod, output logic signed [7:0] quotient,
                           output logic signed [7:0] remainder);
  assign sum = a + b;
  assign diff = a - b;
  assign prod = a * b;
  assign quotient = a / b;
  assign remainder = a % b;
endmodule
module comp_ops(input logic [7:0] a, input logic [7:0] b,
                output logic eq, output logic neq,
                output logic lt, output logic lte,
                output logic gt, output logic gte);
  assign eq  = (a == b);
  assign neq = (a != b);
  assign lt  = (a < b);
  assign lte = (a <= b);
  assign gt  = (a > b);
  assign gte = (a >= b);
endmodule
module unary_reduce(input logic [3:0] a,
                    output logic [3:0] not_a, output logic [3:0] neg_a,
                    output logic and_red, output logic or_red, output logic xor_red);
  assign not_a   = ~a;
  assign neg_a   = -a;
  assign and_red = &a;
  assign or_red  = |a;
  assign xor_red = ^a;
endmodule
module concat_rep(input logic [3:0] a, input logic [3:0] b,
                  output logic [7:0] out_concat, output logic [11:0] out_rep);
  assign out_concat = {a, b};
  assign out_rep    = {3{a}};
endmodule
module slice_dynamic(input logic [7:0] in, input logic [2:0] idx,
                     output logic bit_sel, output logic [3:0] part_sel);
  assign bit_sel  = in[idx];
  assign part_sel = in[idx +: 4];
endmodule
module ternary_mux(input logic sel, input logic [7:0] a, input logic [7:0] b,
                   output logic [7:0] out_mux);
  assign out_mux = sel ? a : b;
endmodule
module cast_ops(input logic signed [7:0] a, input logic [7:0] b,
                output logic signed [7:0] out_signed, output logic [7:0] out_unsigned);
  assign out_signed   = $signed(b);
  assign out_unsigned = $unsigned(a);
endmodule
module special_funcs #(parameter N = 16)(
  input  logic [N-1:0] a,
  output logic [$clog2(N)-1:0] clg2_val,
  output logic [3:0] ones_cnt
);
  assign clg2_val = $clog2(N);
  assign ones_cnt = $countones(a);
endmodule
module real_bits(input real r_in, input logic [63:0] bits_in,
                 output logic [63:0] bits_out, output real r_out);
  assign bits_out = $realtobits(r_in);
  always_comb r_out = $bitstoreal(bits_in);
endmodule
module param_array_sel #(parameter DEPTH = 8, parameter WIDTH = 8)(
  input  logic [WIDTH-1:0] mem [DEPTH-1:0],
  input  logic [$clog2(DEPTH)-1:0] addr,
  output logic [WIDTH-1:0] data_out
);
  assign data_out = mem[addr];
endmodule
