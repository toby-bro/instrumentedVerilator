`define WIDTH 8
module m1(input logic [WIDTH-1:0] in, output logic [WIDTH-1:0] out);
  assign out = in;
endmodule
`undef WIDTH
`define ADD(a,b) ((a)+(b))
module m_add(input logic [3:0] a, input logic [3:0] b, output logic [4:0] sum);
  assign sum = `ADD(a,b);
endmodule
`undef ADD
`define foo 1
`define bar 2
`define JOINER foo``bar
module m_jtest(input logic in, output logic out);
  localparam int val = `JOINER;
  assign out = in ? val[0] : ~val[0];
endmodule
`undef foo
`undef bar
`undef JOINER
`define FOO
module m_ifdef1(input logic a, output logic b);
`ifdef FOO
  assign b = a;
`else
  assign b = ~a;
`endif
endmodule
`undef FOO
module m_ifndef1(input logic a, output logic b);
`ifndef BAR
  assign b = a;
`endif
endmodule
`define X 0
module m_ifexpr(input logic a, output logic b);
`ifdef(X)
  assign b = 1;
`else
  assign b = 0;
`endif
endmodule
`undef X
module m_branch(input logic a, output logic b);
`ifdef A
  assign b = 1;
`elsif B
  assign b = 2;
`else
  assign b = 3;
`endif
endmodule
`define DFLT(x=1) x*2
module m_default(input logic [3:0] in, output logic [4:0] out);
  assign out = `DFLT();
endmodule
`undef DFLT
module m_comments(input logic a, output logic b);
/*verilator full_case*/ /*cadence optimize*/ /*pragma synthesis*/ 
  assign b = a;
endmodule
`line 200 "syn.v"
module m_line(input logic a, output logic b);
  assign b = a;
endmodule
`define A 10
`define B A
module m_nested(input logic [3:0] in, output logic [3:0] out);
  assign out = `B;
endmodule
`undef B
`undef A
`define X1 1
`define X2 2
`UNDEFINEALL
module m_afterundef(input logic a, output logic b);
`ifdef X1
  assign b = 0;
`else
  assign b = 1;
`endif
endmodule
