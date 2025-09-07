package pkg_ex;
  typedef logic signed [3:0] my_signed_t;
  typedef struct packed { my_signed_t a; logic b; } my_struct_t;
  typedef union packed { logic [7:0] u; logic signed [7:0] s; } my_union_t;
  typedef enum logic [1:0] { RED = 2'b00, GREEN = 2'b01, BLUE = 2'b10 } color_t;
  function automatic int inc(input int x); inc = x + 1; endfunction
endpackage
import pkg_ex::*;
interface simple_if #(parameter int WIDTH = 8) (input logic clk);
  logic [WIDTH-1:0] data;
endinterface
module param_int #(parameter int P = 4) (
  input logic [P-1:0] in,
  output logic [P-1:0] out
);
  assign out = in;
endmodule
module param_real #(parameter real R = 1.23) (
  input real in,
  output real out
);
  assign out = in * R;
endmodule
module param_string #(parameter string S = "sv") (
  input logic [7:0] in,
  output logic [7:0] out
);
  localparam int LEN = S.len();
  assign out = in;
endmodule
module param_type #(parameter type T = logic [7:0]) (
  input T in,
  output T out
);
  assign out = in;
endmodule
module complex_param #(
  parameter int N = 3,
  parameter color_t C = BLUE
) (
  input logic [N-1:0] in,
  output logic [7:0] out_byte
);
  generate
    if (C == GREEN) begin : green_blk
      assign out_byte = {8{1'b1}};
    end else begin : oth_blk
      assign out_byte = {{8-N{1'b0}}, in};
    end
  endgenerate
endmodule
module gen_for_example (
  input logic clk,
  input logic [3:0] inbus,
  output logic [3:0] outbus
);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : genfor_blk
      assign outbus[i] = inbus[i];
    end
  endgenerate
endmodule
module gen_case_example #(
  parameter int G = 1
) (
  input logic [1:0] sel,
  input logic [7:0] d0, d1, d2,
  output logic [7:0] dout
);
  generate
    case (sel)
      2'b00: assign dout = d0;
      2'b01: assign dout = d1;
      default: assign dout = d2;
    endcase
  endgenerate
endmodule
module interface_port #(
  parameter int W = 8
) (
  input logic clk,
  interface simple_if #(W) if0,
  output logic [W-1:0] y
);
  assign y = if0.data;
endmodule
module struct_unpack #(
  parameter int M = 2
) (
  input  logic [M-1:0] arr2d [1:0],
  output logic [M-1:0] arr2d_out [1:0]
);
  assign arr2d_out = arr2d;
endmodule
module typedef_enum (
  input my_signed_t in_val,
  output color_t out_col
);
  assign out_col = (in_val > 0) ? GREEN : RED;
endmodule
module function_use (
  input my_signed_t a,
  output my_signed_t b
);
  assign b = inc(a);
endmodule
