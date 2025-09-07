module mod_and #(parameter W = 8) (input logic [W-1:0] a, b, output logic [W-1:0] y);
  assign y = a & b;
endmodule
module mod_or #(parameter W = 8) (input logic [W-1:0] a, b, output logic [W-1:0] y);
  assign y = a | b;
endmodule
module mod_xor #(parameter W = 8) (input logic [W-1:0] a, b, output logic [W-1:0] y);
  assign y = a ^ b;
endmodule
module mod_not (input logic [7:0] a, output logic [7:0] y);
  assign y = ~a;
endmodule
module mod_neg (input logic signed [7:0] a, output logic signed [7:0] y);
  assign y = -a;
endmodule
module mod_add (input logic [7:0] a, b, output logic [7:0] y);
  assign y = a + b;
endmodule
module mod_sub (input logic [7:0] a, b, output logic [7:0] y);
  assign y = a - b;
endmodule
module mod_mul (input logic [3:0] a, b, output logic [7:0] y);
  assign y = a * b;
endmodule
module mod_div (input logic [7:0] a, b, output logic [7:0] y);
  assign y = a / b;
endmodule
module mod_mod (input logic [7:0] a, b, output logic [7:0] y);
  assign y = a % b;
endmodule
module mod_shift_left (input logic [7:0] a, input logic [2:0] s, output logic [7:0] y);
  assign y = a << s;
endmodule
module mod_shift_right (input logic [7:0] a, input logic [2:0] s, output logic [7:0] y);
  assign y = a >> s;
endmodule
module mod_sel_const (input logic [7:0] a, output logic y);
  assign y = a[3];
endmodule
module mod_sel_range (input logic [7:0] a, output logic [3:0] y);
  assign y = a[7:4];
endmodule
module mod_indexed_sel (input logic [7:0] a, input logic [2:0] idx, output logic y);
  assign y = a[idx];
endmodule
module mod_concat (input logic [3:0] a, b, input logic [1:0] c, output logic [9:0] y);
  assign y = {a, b, c};
endmodule
module mod_nested_concat (input logic [1:0] a, b, input logic [3:0] c, output logic [7:0] y);
  assign y = {{a, b}, c};
endmodule
module mod_replicate (input logic [1:0] a, output logic [7:0] y);
  assign y = {4{a}};
endmodule
module mod_reduce (input logic [7:0] a, output logic y_and, y_or, y_xor);
  assign y_and = &a;
  assign y_or  = |a;
  assign y_xor = ^a;
endmodule
module mod_conditional (input logic sel, input logic [7:0] a, b, output logic [7:0] y);
  assign y = sel ? a : b;
endmodule
module mod_if_comb (input logic sel, input logic [7:0] a, b, output logic [7:0] y);
  always_comb begin
    if (sel)
      y = a;
    else
      y = b;
  end
endmodule
module mod_lhs_concat (input logic [7:0] in, output logic [3:0] hi, lo);
  always_comb {hi, lo} = in;
endmodule
module mod_multiple_out (input logic [3:0] a, b, output logic [3:0] y1, y2);
  assign {y1, y2} = {a, b};
endmodule
module mod_array_sel (input logic [7:0] arr [0:3], output logic [7:0] y);
  assign y = arr[2];
endmodule
module mod_indexed_array_sel (input logic [7:0] arr [0:3], input logic [1:0] idx, output logic [7:0] y);
  assign y = arr[idx];
endmodule
module mod_partselect_assign (input logic [7:0] in, output logic [3:0] hi, lo);
  always_comb begin
    hi = in[7:4];
    lo = in[3:0];
  end
endmodule
module mod_unpack_concat (input logic [7:0] in, output logic [3:0] h, m, l);
  always_comb begin
    {h, m, l} = {in[7:6], in[5:3], in[2:0]};
  end
endmodule
module mod_mixed_ops (input logic [3:0] a, b, input logic [1:0] c, output logic [5:0] y);
  assign y = (a + b) ^ c;
endmodule
module mod_signed_compare (input logic signed [7:0] a, b, output logic gt, eq);
  assign gt = (a > b);
  assign eq = (a == b);
endmodule
module mod_concat_if (input logic flag, input logic [3:0] x, y, output logic [7:0] z);
  always_comb begin
    if (flag)
      z = {x, y};
    else
      z = {y, x};
  end
endmodule
module mod_sel_dynamic_part (input logic [15:0] a, input logic [3:0] pos, output logic [3:0] y);
  assign y = a[pos +: 4];
endmodule
