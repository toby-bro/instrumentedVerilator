typedef struct packed { logic [3:0] a; logic [3:0] b; } my_struct_t;
typedef union packed { logic [7:0] a; logic [7:0] b; } my_union_t;
class Base;
  function int calc(int x);
    return x + 1;
  endfunction
endclass
class Derived extends Base;
  function int calc(int x);
    return x * 2;
  endfunction
  static function int stat(int x);
    return x + 3;
  endfunction
  int member;
endclass
module uni_ops(input logic [3:0] in, output logic [3:0] out_not, output logic out_and_rdc, output logic out_or_rdc);
  assign out_not     = ~in;
  assign out_and_rdc = &in;
  assign out_or_rdc  = |in;
endmodule
module bi_ops(input logic signed [7:0] a, input logic signed [7:0] b,
              output logic signed [8:0] out_add, output logic signed [8:0] out_sub,
              output logic lt, output logic gt,
              output logic [7:0] out_and_bit, output logic [7:0] out_or_bit, output logic [7:0] out_xor_bit);
  assign out_add     = a + b;
  assign out_sub     = a - b;
  assign lt          = a < b;
  assign gt          = a > b;
  assign out_and_bit = a & b;
  assign out_or_bit  = a | b;
  assign out_xor_bit = a ^ b;
endmodule
module cond_ops(input logic [7:0] x, input logic [7:0] y, input logic [7:0] z,
                output logic [7:0] out1, output logic [7:0] out2);
  assign out1 = (x > y) ? x : y;
  assign out2 = (x > y) ? ((x > z) ? x : z) : y;
endmodule
module quad_concat(input logic [7:0] a, input logic [7:0] b, input logic [7:0] c, input logic [7:0] d,
                   output logic [31:0] out);
  assign out = {a, b, c, d};
endmodule
module cast_ops(input logic [7:0] small, output logic signed [15:0] signed_ext, output logic [15:0] zero_ext);
  assign signed_ext = {{8{small[7]}}, small};
  assign zero_ext   = {8'b0, small};
endmodule
module var_shift(input logic [7:0] x, output logic [31:0] y);
  assign y = x << 30;
endmodule
module const_ops(input logic dummy, output logic [31:0] y1, output logic [31:0] y2, output logic [31:0] y3);
  assign y1 = 1;
  assign y2 = -1;
  assign y3 = 32'd15;
endmodule
module struct_sel(input my_struct_t s_in, output logic [3:0] out_a, output logic [3:0] out_b);
  assign out_a = s_in.a;
  assign out_b = s_in.b;
endmodule
module union_sel(input my_union_t u_in, output logic [7:0] a_out, output logic [7:0] b_out);
  assign a_out = u_in.a;
  assign b_out = u_in.b;
endmodule
module named_struct(input logic [3:0] in1, input logic [3:0] in2,
                    output logic [3:0] out1, output logic [3:0] out2);
  wire my_struct_t s;
  assign s = '{in1, in2};
  assign out1 = s.a;
  assign out2 = s.b;
endmodule
module expr_stmt(input logic [3:0] in, output logic [3:0] out);
  always_comb begin
    out = in + 0;
  end
endmodule
module class_dyn(input logic [3:0] in, output logic [7:0] out);
  Base c;
  Derived d;
  always_comb begin
    d = new();
    c = d;
    out = c.calc(in);
  end
endmodule
module class_hard(input logic [3:0] in, output int out);
  always_comb begin
    out = Derived::stat(in);
  end
endmodule
module null_check(input logic [3:0] in, output logic [7:0] out);
  Derived c;
  always_comb begin
    c = new();
    out = c.calc(in);
  end
endmodule
module member_sel(input logic [3:0] in, output int out);
  Derived c;
  always_comb begin
    c = new();
    c.member = in;
    out = c.member;
  end
endmodule
