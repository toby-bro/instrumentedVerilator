package my_pkg;
  typedef logic [15:0] word_t;
endpackage
interface bus_if(input logic clk);
  logic [7:0] data;
  modport slave (input data);
endinterface
module AstNodeModuleEx #(parameter N = 8)(
  input  logic [N-1:0] in,
  output logic [N-1:0] out
);
  assign out = in;
endmodule
module AstAlwaysEx(
  input  logic clk,
  input  logic rst,
  output logic flag
);
  always_ff @(posedge clk or posedge rst) begin
    if (rst) flag <= 1'b0;
    else     flag <= ~flag;
  end
endmodule
module AstNodeAssignEx(
  input  logic a,
  input  logic b,
  output logic y
);
  logic tmp;
  assign tmp = a & b;
  assign y   = tmp;
endmodule
module AstVarXRefEx(
  input  logic in0,
  output logic out0
);
  logic w_orig;
  logic w_alias;
  assign w_orig  = in0;
  assign w_alias = w_orig;
  assign out0    = w_alias;
endmodule
module AstNodeFTaskRefEx(
  input  logic x,
  input  logic y,
  output logic z
);
  task automatic mytask(input logic a, input logic b, output logic c);
    c = a | b;
  endtask
  always_comb begin
    mytask(x, y, z);
  end
endmodule
module AstPragmaEx(
  input  logic [3:0] in,
  output logic [3:0] out
);
  (* KEEP = "TRUE" *) logic [3:0] temp;
  assign temp = in;
  assign out  = temp;
endmodule
module TypedefEx(
  input  logic [7:0] in,
  output logic       ready
);
  typedef struct packed { logic [3:0] a; logic [3:0] b; } half_t;
  half_t data;
  assign data.a = in[7:4];
  assign data.b = in[3:0];
  assign ready  = &data.a;
endmodule
module IfaceRefDTypeEx(
  input  logic       clk,
  input  logic [7:0] bus_din,
  output logic [7:0] dout
);
  bus_if bus_if_inst(.clk(clk));
  assign bus_if_inst.data = bus_din;
  always_ff @(posedge clk) begin
    dout <= bus_if_inst.data;
  end
endmodule
module CoverDeclEx(
  input  logic clk,
  input  logic en,
  output logic cov
);
  covergroup cg @(posedge clk);
    coverpoint en;
  endgroup
  cg cg_inst = new();
  always_ff @(posedge clk) begin
    cg_inst.sample();
  end
  assign cov = en;
endmodule
import my_pkg::*;
module PackageEx(
  input  word_t a,
  input  word_t b,
  output word_t sum
);
  assign sum = a + b;
endmodule
module GenIfEx #(parameter SEL = 1)(
  input  logic a,
  input  logic b,
  output logic y
);
  generate
    if (SEL) assign y = a;
    else     assign y = b;
  endgenerate
endmodule
module GenForEx #(parameter N = 4)(
  input  logic [N-1:0] in,
  output logic [N-1:0] out
);
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin
      assign out[i] = ~in[i];
    end
  endgenerate
endmodule
module ClassEx(
  input  logic clk,
  input  logic reset,
  input  logic in,
  output logic out
);
  class Counter;
    int c;
    function new(int init); c = init; endfunction
    function int tick(int inc); c += inc; return c; endfunction
  endclass
  Counter cnt;
  always_ff @(posedge clk or posedge reset) begin
    if (reset)   cnt = new(0);
    else         out <= (cnt.tick(1) > 10);
  end
endmodule
module TaskFuncEx(
  input  logic [3:0] a,
  input  logic [3:0] b,
  output logic [4:0] sum,
  output logic [3:0] maxv
);
  function automatic [4:0] add(input logic [3:0] x, input logic [3:0] y);
    add = x + y;
  endfunction
  task automatic find_max(input logic [3:0] x, input logic [3:0] y, output logic [3:0] m);
    if (x > y) m = x;
    else       m = y;
  endtask
  assign sum = add(a, b);
  always_comb find_max(a, b, maxv);
endmodule
module AssertEx(
  input  logic clk,
  input  logic sig,
  output logic err
);
  logic err_flag;
  always_ff @(posedge clk) begin
    if (!sig) err_flag <= 1'b1;
  end
  assign err = err_flag;
endmodule
