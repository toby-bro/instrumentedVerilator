module m_clkblk(input  logic clk,
                input  logic in,
                output logic out);
  clocking cb_default @(posedge clk);
    input  in;
    output out;
  endclocking
  always @(cb_default) out <= cb_default.in;
endmodule
module m_disable(input  logic clk,
                 input  logic reset,
                 input  logic a,
                 output logic y);
  default disable iff (reset);
  property p; @(posedge clk) a |-> ##1 a; endproperty
  assert property (p);
  assign y = reset;
endmodule
module m_prop(input  logic clk,
              input  logic x,
              output logic y_fell,
              output logic y_rose,
              output logic y_stable,
              output logic y_past);
  property p_fell; @(posedge clk) $fell(x); endproperty
  property p_rose; @(posedge clk) $rose(x); endproperty
  property p_stable; @(posedge clk) $stable(x); endproperty
  property p_past; @(posedge clk) $past(x); endproperty
  assert property (p_fell);
  assert property (p_rose);
  assert property (p_stable);
  assert property (p_past);
  assign y_fell   = x;
  assign y_rose   = x;
  assign y_stable = x;
  assign y_past   = x;
endmodule
module m_imply(input  logic clk,
               input  logic a,
               input  logic b,
               output logic y);
  sequence seq_ab; a ##1 b; endsequence
  property prop_imp; @(posedge clk) seq_ab |-> ##2 a; endproperty
  assert property (prop_imp);
  assign y = a;
endmodule
module m_cover(input  logic clk,
               input  logic a,
               input  logic b,
               output logic cv);
  property cp; @(posedge clk) a ##1 b; endproperty
  cover property (cp);
  assign cv = a;
endmodule
module m_assign_delay(input  logic clk,
                      input  logic a,
                      output logic r);
  clocking cb @(posedge clk);
    input a;
  endclocking
  always @(cb) r <= cb.a;
endmodule
module m_class_inst(input  logic clk,
                    input  logic reset,
                    input  logic [7:0] in,
                    output logic [7:0] out);
  class C;
    int v;
    function void set(int i); v = i; endfunction
    function int get(); return v; endfunction
  endclass
  always @(posedge clk) begin
    static C c_inst = new();
    c_inst.set(in);
    out <= c_inst.get();
  end
endmodule
module m_fork(input  logic clk,
              input  logic a,
              output logic p,
              output logic q);
  always @(posedge clk) fork
    p <= a;
    q <= ~a;
  join_none;
endmodule
module m_struct(input  logic clk,
                input  logic [3:0] data,
                output logic bit_out);
  typedef struct packed { logic [3:0] f; } S;
  S s_inst;
  assign s_inst.f = data;
  always @(posedge clk) bit_out <= s_inst.f[0];
endmodule
