module mod_default_join(input logic a, input logic clk, output logic b);
  always @(posedge clk) begin
    logic x;
    fork
      x = a;
      b = x;
    join
  end
endmodule
module mod_join_none(input logic a, input logic clk, output logic b);
  always @(posedge clk) begin
    fork
      b = a;
    join_none
  end
endmodule
module mod_join_any(input logic a, input logic clk, output logic b);
  always @(posedge clk) begin
    fork
      if (a)
        b = 1'b1;
      else
        b = 1'b0;
    join_any
  end
endmodule
module mod_nested_forks(input logic a, input logic clk, output logic b);
  always @(posedge clk) begin
    logic y;
    fork
      fork
        y = ~a;
      join
      b = y;
    join
  end
endmodule
module mod_taskdef_call(input logic a, input logic clk, output logic b);
  task automatic do_task(input logic in, output logic outp);
    outp = in;
  endtask
  always @(posedge clk) begin
    logic temp;
    do_task(a, temp);
    fork
      b = temp;
    join
  end
endmodule
module mod_timing_fork(input logic clk, input logic a, output logic b);
  always @(posedge clk) begin
    fork
      @(posedge clk) b = a;
    join_none
  end
endmodule
module mod_function_call(input logic a, input logic clk, output logic b);
  function automatic logic f1(input logic in);
    f1 = ~in;
  endfunction
  always @(posedge clk) begin
    fork
      b = f1(a);
    join
  end
endmodule
module mod_inout(input logic a, inout logic io, output logic b);
  always @* begin
    fork
      io = a;
      b = io;
    join_any
  end
endmodule
