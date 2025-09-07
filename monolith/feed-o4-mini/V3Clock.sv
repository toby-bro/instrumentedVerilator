module FlipFlop(input logic clk, input logic d, output logic q);
  always_ff @(posedge clk) begin
    q <= d;
  end
endmodule
module EdgeDetector(input logic clk, input logic reset_n, input logic signal, output logic out1, output logic out2);
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      out1 <= 1'b0;
      out2 <= 1'b1;
    end else begin
      out1 <= signal;
      out2 <= ~signal;
    end
  end
endmodule
module CombLogic(input logic [3:0] a, input logic [3:0] b, output logic y_and, output logic y_or, output logic eq, output logic ne);
  always_comb begin
    y_and = a & b;
    y_or  = a | b;
    eq    = (a == b);
    ne    = (a != b);
  end
endmodule
module GenModule #(parameter WIDTH = 4) (input logic clk, input logic [WIDTH-1:0] in, output logic [WIDTH-1:0] out);
  genvar i;
  generate
    for (i = 0; i < WIDTH; i = i + 1) begin: gen_loop
      always_ff @(posedge clk) begin
        out[i] <= in[i];
      end
    end
  endgenerate
endmodule
module FuncModule(input logic a, input logic b, output logic y);
  function logic imp(input logic x, input logic z);
    imp = (~x) | z;
  endfunction
  assign y = imp(a, b);
endmodule
module TaskModule(input logic clk, input logic a, output logic y);
  task automatic mytask(input logic x, output logic z);
    z = x & (~x);
  endtask
  always_ff @(posedge clk) begin
    mytask(a, y);
  end
endmodule
module NestedIf(input logic a, input logic b, input logic c, output logic y);
  always_comb begin
    if (a) begin
      if (b) begin
        y = c;
      end else begin
        y = ~c;
      end
    end else begin
      y = 1'b0;
    end
  end
endmodule
module WhileLoop(input logic clk, input logic en, output logic [3:0] cnt);
  always_ff @(posedge clk) begin
    cnt = 4'd0;
    while (en && cnt < 4) begin
      cnt = cnt + 1;
    end
  end
endmodule
module DoWhile(input logic clk, input logic en, output logic [3:0] cnt);
  always_ff @(posedge clk) begin
    cnt = 4'd0;
    do begin
      cnt = cnt + 1;
    end while (en && cnt < 4);
  end
endmodule
module ForLoop(input logic clk, output logic [3:0] arr);
  integer i;
  always_ff @(posedge clk) begin
    for (i = 0; i < 4; i = i + 1) begin
      arr[i] <= i[0];
    end
  end
endmodule
