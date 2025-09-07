module op_and #(parameter W = 8) (input  logic [W-1:0] a, b, output logic [W-1:0] y);
  assign y = a & b;
endmodule
module op_or #(parameter W = 8) (input  logic [W-1:0] a, b, output logic [W-1:0] y);
  assign y = a | b;
endmodule
module op_xor #(parameter W = 8) (input  logic [W-1:0] a, b, output logic [W-1:0] y);
  assign y = a ^ b;
endmodule
module op_not #(parameter W = 4) (input  logic [W-1:0] a, output logic [W-1:0] y);
  assign y = ~a;
endmodule
module op_red_and #(parameter W = 4) (input  logic [W-1:0] a, output logic y);
  assign y = &a;
endmodule
module op_red_or #(parameter W = 4) (input  logic [W-1:0] a, output logic y);
  assign y = |a;
endmodule
module op_red_xor #(parameter W = 4) (input  logic [W-1:0] a, output logic y);
  assign y = ^a;
endmodule
module op_add #(parameter W = 8) (input  logic [W-1:0] a, b, output logic [W-1:0] sum);
  assign sum = a + b;
endmodule
module op_sub #(parameter W = 8) (input  logic [W-1:0] a, b, output logic [W-1:0] diff);
  assign diff = a - b;
endmodule
module op_mul #(parameter W = 8) (input  logic [W-1:0] a, b, output logic [2*W-1:0] prod);
  assign prod = a * b;
endmodule
module op_div #(parameter W = 8) (input  logic [W-1:0] a, b, output logic [W-1:0] quot);
  assign quot = a / b;
endmodule
module op_mod #(parameter W = 8) (input  logic [W-1:0] a, b, output logic [W-1:0] rem);
  assign rem = a % b;
endmodule
module op_eq #(parameter W = 8) (input  logic [W-1:0] a, b, output logic y);
  assign y = (a == b);
endmodule
module op_neq #(parameter W = 8) (input  logic [W-1:0] a, b, output logic y);
  assign y = (a != b);
endmodule
module op_cmp4 #(parameter W = 8) (input  logic [W-1:0] a, b, output logic lt, ge);
  assign lt = (a < b);
  assign ge = (a >= b);
endmodule
module op_mux8 (input  logic [7:0] d0, d1, input logic sel, output logic [7:0] y);
  assign y = sel ? d1 : d0;
endmodule
module op_concat4 (input  logic [3:0] lo, hi, output logic [7:0] y);
  assign y = {hi, lo};
endmodule
module op_replicate2to8 (input  logic [1:0] a, output logic [7:0] y);
  assign y = {4{a}};
endmodule
module op_const_bit_sel (input  logic [7:0] a, output logic y);
  assign y = a[3];
endmodule
module op_var_bit_sel (input  logic [7:0] a, input logic [2:0] idx, output logic y);
  assign y = a[idx];
endmodule
module op_array_const (input  logic [3:0] arr [0:3], output logic [3:0] y);
  assign y = arr[2];
endmodule
module op_array_var (input  logic [3:0] arr [0:3], input logic [1:0] idx, output logic [3:0] y);
  assign y = arr[idx];
endmodule
module op_sign_ext (input  logic signed [7:0] a, output logic signed [15:0] y);
  assign y = a;
endmodule
module op_neg #(parameter W = 8) (input  logic signed [W-1:0] a, output logic signed [W-1:0] y);
  assign y = -a;
endmodule
module op_shift (input  logic [7:0] a, input logic [2:0] sh,
                 output logic [7:0] lsh, rsh, output logic signed [7:0] ash);
  assign lsh = a << sh;
  assign rsh = a >> sh;
  assign ash = $signed(a) >>> sh;
endmodule
module proc_always_comb_add (input  logic [3:0] a, b, output logic [3:0] y);
  always_comb y = a + b;
endmodule
module proc_if_else (input  logic [7:0] a, b, input logic sel, output logic [7:0] y);
  always_comb begin
    if (sel)
      y = a;
    else
      y = b;
  end
endmodule
module proc_lhs_concat (input  logic [3:0] in,
                        output logic [1:0] hi,
                        output logic [1:0] lo);
  always_comb {hi, lo} = in;
endmodule
module proc_lhs_array_concat (input  logic [1:0] a, b,
                              output logic [3:0] cab);
  always_comb cab = {a, b};
endmodule
module op_signed_cast (input  logic [3:0] a, output logic [3:0] y);
  assign y = $signed(a);
endmodule
module op_triplicate (input logic [1:0] a, output logic [5:0] y);
  assign y = {3{a}};
endmodule
module op_sel_variable_concat (input logic [3:0] a, input logic [1:0] sel, output logic [1:0] y);
  assign y = (sel == 2'd0) ? a[1:0]
              : (sel == 2'd1) ? a[3:2]
              : 2'b00;
endmodule
module op_nested_concat (input logic [1:0] a, b, c, output logic [5:0] y);
  assign y = { {2{a}}, b, c };
endmodule
module op_multi_eq (input logic [3:0] a, b, c, output logic eqab, eqbc);
  assign eqab = (a == b);
  assign eqbc = (b == c);
endmodule
module op_shift_or (input logic [7:0] a, input logic [2:0] sh, output logic [7:0] y);
  assign y = (a << sh) | (a >> sh);
endmodule
module op_shift_xor (input logic [7:0] a, input logic [2:0] sh, output logic [7:0] y);
  assign y = (a <<< sh) ^ (a >>> sh);
endmodule
module op_bitwise_mix (input logic [3:0] a, b, input logic sel, output logic [3:0] y);
  assign y = sel ? (a & b) : (a | b);
endmodule
module op_complex_cond (input logic [7:0] a, b, input logic sel1, sel2, output logic [7:0] y);
  assign y = sel1 ? (sel2 ? a : b) : (sel2 ? b : a);
endmodule
module op_array_of_vectors (input logic [1:0] m [0:3], input logic [1:0] idx, output logic [1:0] y);
  assign y = m[idx];
endmodule
module op_concat_lhs_vector (input logic [7:0] v, output logic [3:0] vhi, vlo);
  always_comb {vhi, vlo} = v;
endmodule
