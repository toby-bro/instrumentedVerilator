module m_simple(input logic [3:0] a, input logic [3:0] b, output logic [3:0] c);
  assign c = a & b;
endmodule
module m_sel(input logic [15:0] in, input logic [3:0] idx, output logic bit0, output logic [7:0] part);
  assign bit0 = in[idx];
  assign part = in[idx +: 8];
endmodule
module m_concat(input logic [7:0] a, input logic [7:0] b, input logic [7:0] c, output logic [23:0] out);
  assign out = {a, b, c};
endmodule
module m_if(input logic en, input logic [7:0] x, input logic [7:0] y, output logic [7:0] z);
  always_comb begin
    if (en) z = x; else z = y;
  end
endmodule
module m_cond(input logic sel, input logic [7:0] x, input logic [7:0] y, output logic [7:0] z);
  assign z = sel ? x : y;
endmodule
module m_act(input logic clk, input logic [7:0] din, output logic [7:0] q);
  always_ff @(posedge clk) begin
    q <= din + 1;
  end
endmodule
module m_fork(input logic in, output logic a, output logic b_out);
  always_comb begin
    fork_task(in, a, b_out);
  end
  task automatic fork_task(input logic in, input logic a, input logic b_out);
    fork
      a = in;
      b_out = ~in;
    join
  endtask
endmodule
module m_dpi(input int a, output int b);
  import "DPI-C" function int cfunc(input int val);
  assign b = cfunc(a);
endmodule
module m_await(input logic cond, output logic out);
  always_comb begin
    do_await(cond, out);
  end
  task automatic do_await(input logic cond, output logic outp);
    wait (cond);
    outp = cond ? 1'b1 : 1'b0;
  endtask
endmodule
module m_expr(input logic [3:0] p, input logic [3:0] q, output logic [3:0] r);
  assign r = (p + q) ^ (p & q);
endmodule
