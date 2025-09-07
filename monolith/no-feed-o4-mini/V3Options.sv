`timescale 1ns/1ps
`ifndef MACRO_INVERT
`define MACRO_INVERT(x) (~(x))
`endif
package my_pkg;
  typedef struct { int a; int b; } my_struct_t;
  function int add(int x, int y);
    add = x + y;
  endfunction
endpackage
interface simple_if(input logic clk);
  logic req;
  logic ack;
  modport master(input req, output ack);
endinterface
module sub_gen #(parameter int IDX = 0) (
  input  logic in,
  output logic out
);
  assign out = in ^ IDX;
endmodule
module macro_param_demo #(
  parameter int WIDTH = 8
) (
  input  logic [WIDTH-1:0] in,
  output logic [WIDTH-1:0] out
);
  assign out = `MACRO_INVERT(in);
endmodule
module gen_loop_demo #(
  parameter int N = 4
) (
  input  logic [N-1:0] in,
  output logic [N-1:0] out
);
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin : genblk
      sub_gen #(.IDX(i)) u_sub (
        .in(in[i]),
        .out(out[i])
      );
    end
  endgenerate
endmodule
module gen_if_demo #(
  parameter bit HAS_EXTRA = 1
) (
  input  logic in,
  output logic out
);
  generate
    if (HAS_EXTRA) begin : extra
      assign out = in;
    end else begin : noextra
      assign out = ~in;
    end
  endgenerate
endmodule
module class_inst_demo (
  input  logic [3:0] in,
  output logic [3:0] out
);
  class MyClass;
    function new(); endfunction
    function logic [3:0] process(logic [3:0] x);
      return x + 1;
    endfunction
  endclass
  MyClass c;
  always_comb begin
    c = new;
    out = c.process(in);
  end
endmodule
module pkg_use_demo (
  input  logic [7:0] a,
  input  logic [7:0] b,
  output logic [7:0] sum
);
  import my_pkg::*;
  my_struct_t s;
  always_comb begin
    s = '{a, b};
    sum = add(s.a, s.b);
  end
endmodule
module string_demo (
  input  logic       clk,
  input  logic       valid,
  output string      status
);
  always_ff @(posedge clk) begin
    if (valid)
      status = "GOOD";
    else
      status = "BAD";
  end
endmodule
module if_demo (
  input  logic         clk,
  input  simple_if.master intf,
  output logic         ack_out
);
  always_ff @(posedge clk) begin
    intf.ack <= intf.req;
    ack_out <= intf.ack;
  end
endmodule
module coverage_demo (
  input  logic        clk,
  input  logic [7:0]  data,
  output logic        hit
);
  covergroup cg @(posedge clk);
    coverpoint data;
  endgroup
  cg cg_inst = new;
  always_ff @(posedge clk) begin
    cg_inst.sample();
    hit <= (data >= 8'h80);
  end
endmodule
module assert_demo (
  input  logic [3:0] in,
  output logic       ok
);
  always_comb begin
    assert (in < 4);
    ok = (in < 4);
  end
endmodule
