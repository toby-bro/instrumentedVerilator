module WideExpr(input logic [127:0] a, input logic [127:0] b, output logic [255:0] out);
  assign out = {a, b} + {b, a};
endmodule
module Shifts(input logic [7:0] a, input logic [7:0] sh_small, input logic [7:0] sh_large, output logic [7:0] out_sl, output logic [7:0] out_sr, output logic [7:0] out_sra);
  assign out_sl  = a << sh_small;
  assign out_sr  = a >> sh_small;
  assign out_sra = a >>> sh_small;
  wire [7:0] tmp_sl = a << sh_large;
  wire [7:0] tmp_sr = a >> sh_large;
endmodule
module AssignAtomic(input logic [7:0] in, output logic [7:0] out);
  always_comb begin
    out = in;
  end
endmodule
module AssignNonAtomic(input logic [7:0] in, output logic [7:0] out);
  always_comb begin
    out = out + in;
  end
endmodule
module WhileLoop(input logic [7:0] in, output logic [7:0] out);
  always_comb begin
    out = in;
    while (out != 0) begin
      out = out - 1;
    end
  end
endmodule
module BitSel(input logic [15:0] in, output logic [3:0] out);
  assign out = in[7:4];
endmodule
module ArraySel(input logic [7:0] in [3:0], output logic [7:0] out);
  always_comb begin
    out = in[2];
  end
endmodule
module AssocArray(input logic [7:0] in, output logic [7:0] out);
  logic [7:0] assoc[string];
  always_comb begin
    assoc["key"] = in;
    out = assoc["key"];
  end
endmodule
module TernaryOp(input logic [7:0] cond_in, input logic [7:0] true_val, input logic [7:0] false_val, output logic [7:0] out);
  assign out = cond_in ? true_val : false_val;
endmodule
module ConstTest(input logic [7:0] in, output logic [7:0] out_small, output logic [255:0] out_large);
  localparam logic [7:0] SMALL_CONST = 8'hFF;
  localparam logic [255:0] LARGE_CONST = {32{8'hFF}};
  always_comb begin
    out_small = in + SMALL_CONST;
    out_large = in + LARGE_CONST;
  end
endmodule
module UnaryBiOp(input logic [7:0] in, output logic [7:0] out_not, output logic out_red_and);
  assign out_not = ~in;
  assign out_red_and = &in;
endmodule
module PackedArrayConv(input logic [15:0] packed_in, output logic [7:0] unpacked_out [3:0], output logic [15:0] packed_out);
  assign {unpacked_out[3], unpacked_out[2], unpacked_out[1], unpacked_out[0]} = packed_in;
  assign packed_out = {unpacked_out[0], unpacked_out[1], unpacked_out[2], unpacked_out[3]};
endmodule
module NestedExpr(input logic [3:0] a, input logic [3:0] b, input logic [3:0] c, output logic [7:0] out);
  assign out = (a & b) ^ (~c | (a + b * c));
endmodule
