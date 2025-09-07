module tri_buffer(input logic sel, input logic in, output tri out);
  assign out = sel ? in : 'z;
endmodule
module bufif1_example(input logic in, input logic en, output tri out);
  bufif1(out, in, en);
endmodule
module bufif0_example(input logic in, input logic en, output tri out);
  bufif0(out, in, en);
endmodule
module pullup_pulldown_example(input wire in_data, inout tri neutral, output wire out);
  assign out = in_data;
  pullup(out);
  pulldown(neutral);
endmodule
module pullup_only_example(input wire a, output wire w);
  assign w = a;
  pullup(w);
endmodule
module pulldown_only_example(input wire a, output wire w);
  assign w = a;
  pulldown(w);
endmodule
module case_eq_example(input wire [1:0] a, output wire eq_z, output wire neq0);
  assign eq_z = (a === 2'bzz);
  assign neq0 = (a !== 2'b00);
endmodule
module wor_example(input wire a, input wire b, output wor w);
  assign w = a;
  assign w = b;
endmodule
module wand_example(input wire a, input wire b, output wand w);
  assign w = a;
  assign w = b;
endmodule
module concat_slice_example(
  input logic [3:0] a,
  input logic [3:0] b,
  input logic [2:0] idx,
  output logic out_bit,
  output logic [7:0] concat_ab,
  output logic [3:0] slice_upper
);
  assign concat_ab = {a, b};
  assign slice_upper = concat_ab[7:4];
  assign out_bit = concat_ab[idx];
endmodule
module countones_example(
  input logic [3:0] data,
  input logic sel,
  output logic [3:0] ones,
  output logic [3:0] ones_z
);
  logic [3:0] temp;
  assign temp = sel ? 4'bzzzz : data;
  assign ones   = $countones(data);
  assign ones_z = $countones(temp);
endmodule
module bitwise_z_example(
  input logic [1:0] a,
  input logic [1:0] b,
  output logic [1:0] and_z,
  output logic [1:0] or_z
);
  assign and_z = a & b;
  assign or_z  = a | b;
endmodule
module multi_driver_example(
  input logic a,
  input logic b,
  input logic sel,
  output tri w
);
  assign w = sel      ? a : 'z;
  assign w = (~sel)  ? b : 'z;
endmodule
module gate_primitive_example(
  input wire a,
  input wire b,
  output wire out_and,
  output wire out_or,
  output wire out_nand
);
  and and1(out_and, a, b);
  or  or1(out_or,  a, b);
  nand nand1(out_nand, a, b);
endmodule
module ternary_example(
  input logic sel,
  input logic [1:0] x,
  input logic [1:0] y,
  output logic [1:0] res
);
  assign res = sel ? x : y;
endmodule
module ternary_z_example(
  input logic sel,
  input logic in,
  output tri out
);
  assign out = sel ? in : 'z;
endmodule
module inout_tristate_example(
  input logic a,
  inout tri    bus,
  output logic out
);
  assign bus = a ? 1'b1 : 'z;
  assign out = bus;
endmodule
