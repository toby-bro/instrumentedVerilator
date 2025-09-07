module clocking_demo(input logic clk, input logic in_sig, output logic out_sig);
  default clocking cb @(posedge clk);
    input #1 in_sig;
    output out_sig;
  endclocking
endmodule
module unclocked_demo(input logic a, output logic b);
  assert property (a);
endmodule
module cover_or_assert_demo(input bit clk, input bit in_sig, output bit out_sig);
  cover property (@(posedge clk) in_sig ##1 out_sig);
endmodule
module delay_assert_demo(input logic clk, input logic a, input logic b, output logic y);
  assert property (@(posedge clk) a ##1 b);
endmodule
module sequence_demo(input logic clk, input logic x, input logic reset, output logic y);
  property p_fell; @(posedge clk) $fell(x); endproperty
  property p_rose; @(posedge clk) $rose(x); endproperty
  property p_stable; @(posedge clk) $stable(x); endproperty
  property p_past; @(posedge clk) $past(x) ##1 x; endproperty
  assert property (p_fell);
  assert property (p_rose);
  assert property (p_stable);
  assert property (p_past);
endmodule
module implication_demo(input logic clk, input logic a, input logic b, output logic c);
  assert property (@(posedge clk) a |-> b);
endmodule
module default_disable_demo(input logic clk, input logic g, input logic rst, output logic z);
  default disable iff (rst);
  assert property (@(posedge clk) g |=> z);
endmodule
module property_call_demo(input logic clk, input logic a, input logic b, output logic c);
  property foo(input logic p, input logic q);
    disable iff (p);
    @(posedge clk) p ##1 q;
  endproperty
  assert property (foo(a,b));
endmodule
module struct_member_demo(input bit clk, input struct packed {bit a; bit b;} s, output bit c);
  assign c = s.a;
  always_ff @(posedge clk) c <= s.b;
endmodule
module assign_demo(input logic clk, input logic d, output logic q);
  always_ff @(posedge clk) q <= d;
endmodule
