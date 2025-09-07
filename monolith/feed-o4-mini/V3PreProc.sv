`define SIMPLE_ADD 4'b0011
`define ADD2(a,b) ((a)+(b))
`define JOINXY(x,y) x``y
`define STR(s) `"s`"
`define FLAG
`define A_macro 1'b1
`define B_macro 1'b0
`define TEMP 8'hFF
module simple_define(input logic [3:0] in, output logic [3:0] out);
  assign out = in + `SIMPLE_ADD;
endmodule
module param_define(input logic [7:0] in1, input logic [7:0] in2, output logic [7:0] sum);
  assign sum = `ADD2(in1,in2);
endmodule
module join_define(input logic [1:0] hi_, input logic [1:0] lo, output logic [1:0] out);
  logic [1:0] hi_lo;
  assign hi_lo = hi_;
  assign out = `JOINXY(hi_,lo);
endmodule
module stringify_define(input logic clk, output logic [7:0] dummy);
  localparam string my_str = `STR(hello);
  assign dummy = clk;
endmodule
module ifdef_test(input logic in, output logic out);
`ifdef FLAG
  assign out = in;
`else
  assign out = ~in;
`endif
endmodule
module ifndef_test(input logic in, output logic out);
`ifndef FLAG
  assign out = in;
`else
  assign out = ~in;
`endif
endmodule
module elsif_test(input logic in, output logic out);
`ifdef A_macro
  assign out = in;
`elsif B_macro
  assign out = ~in;
`else
  assign out = 1'b0;
`endif
endmodule
module undef_test(input logic [7:0] in, output logic [7:0] out);
  logic [7:0] t1, t2;
  assign t1 = in & `TEMP;
`undef TEMP
`undefineall
  assign t2 = in;
  assign out = t1 | t2;
endmodule
class Cls;
  int a;
  function new(int v);
    a = v;
  endfunction
endclass
module class_test(input logic [7:0] in, output logic [7:0] out);
  logic [7:0] temp;
  always_comb begin
    static Cls c = new(in);
    temp = c.a;
  end
  assign out = temp;
endmodule
