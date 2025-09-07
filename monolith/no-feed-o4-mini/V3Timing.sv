module EventCtl(input logic clk, input logic rst_n, input logic d, output logic q);
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) q <= 1'b0;
    else q <= d;
  end
endmodule
module WaitStmt(input logic sig, output logic out);
  logic tmp;
  always_ff @(posedge sig) begin
    tmp = sig;
    wait (tmp) begin
      out = tmp;
    end
  end
endmodule
module ForkNone(input logic [1:0] in, output logic [7:0] out);
  always_comb begin
    logic [7:0] local;
    local = in;
    fork
      local = local + 1;
      out = local;
    join_none
    out = local * 2;
  end
endmodule
module ForkAny(input logic [3:0] in, output logic [3:0] out);
  always_comb begin
    logic [3:0] tmp;
    tmp = in;
    fork
      tmp = tmp + 1;
      tmp = tmp + 2;
    join_any
    out = tmp;
  end
endmodule
module ForkAll(input logic en, output logic done);
  always_ff @(posedge en) begin
    fork
      done = 1'b0;
      done = 1'b1;
    join
    done = ~done;
  end
endmodule
module GenFor #(parameter N = 4)(input logic [N-1:0] in, output logic [N-1:0] out);
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin : gen_loop
      assign out[i] = in[N-1-i];
    end
  endgenerate
endmodule
module GenIf(input logic sel, input logic a, input logic b, output logic y);
  generate
    if (1) begin
      assign y = sel ? a : b;
    end else begin
      assign y = 1'b0;
    end
  endgenerate
endmodule
module FuncTask(input logic clk, input logic [7:0] in, output logic [7:0] out);
  function automatic logic [7:0] dbl(input logic [7:0] v);
    dbl = v << 1;
  endfunction
  task automatic inc(input logic [7:0] v, output logic [7:0] r);
    r = v + 1;
  endtask
  always_ff @(posedge clk) begin
    logic [7:0] t1;
    inc(in, t1);
    out <= dbl(t1);
  end
endmodule
module ClassInst(input logic clk, input logic en, output logic done);
  class MyClass;
    function void m(input logic v);
    endfunction
  endclass
  always_ff @(posedge clk) begin
    if (en) begin
      MyClass c = new();
      c.m(en);
      done <= en;
    end
  end
endmodule
module EnumTyp(input logic clk, input logic [1:0] sel, output logic [3:0] out);
  typedef enum logic [1:0] {ID0=2'b00, ID1=2'b01, ID2=2'b10} e_t;
  always_ff @(posedge clk) begin
    e_t state;
    state = sel;
    unique case (state)
      ID0: out <= 4'h0;
      ID1: out <= 4'h1;
      default: out <= 4'hF;
    endcase
  end
endmodule
module DynArray(input logic clk, input logic [1:0] idx, output logic [7:0] out);
  logic [7:0] arr [0:3] = '{8'd10, 8'd20, 8'd30, 8'd40};
  always_ff @(posedge clk) begin
    out <= arr[idx];
  end
endmodule
module NamedEvent(input logic clk, input logic trig, output logic q);
  event ev;
  always @(ev) q = ~q;
  always_ff @(posedge clk) begin
    if (trig) -> ev;
  end
endmodule
module Asserts(input logic clk, input logic rst, input logic in, output logic panic);
  always_ff @(posedge clk or posedge rst) begin
    if (!rst) panic <= 1'b0;
    else assert (in) else panic <= 1'b1;
  end
endmodule
module WaitDyn(input logic clk, input logic en, output logic done);
  logic flag;
  always_ff @(posedge clk) begin
    if (en) begin
      flag <= 1'b1;
      wait (flag == 1'b1);
      done <= flag;
    end
  end
endmodule
