`timescale 1ns/1ps
`define USE_FLAG
package pkg_my;
  function int pkg_add(input int a, input int b);
    return a + b;
  endfunction
endpackage
interface my_ifc(input logic clk, input logic rst);
  logic valid;
  modport master (input clk, rst, output valid);
  modport slave  (input clk, rst, input valid);
endinterface
class C1;
  int x;
  function new(int a = 0);
    x = a;
  endfunction
  function int inc();
    return x + 1;
  endfunction
endclass
module m_case_features(input logic [1:0] sel, input logic in1, input logic in2, input logic in3, output logic out1);
  logic [7:0] tmp;
  always_comb begin
    case(sel)
      2'b00: tmp = {in1,3'b000,4'h0};
      2'b01: tmp = {in2,3'b001,4'h1};
      2'b10: casex(sel)
               2'b1x: tmp = {in3,3'b010,4'h2};
               default: tmp = 8'hEE;
             endcase
      2'b11: casez(sel)
               2'b?1: tmp = {in3,3'b011,4'h3};
               default: tmp = 8'hDD;
             endcase
      default: tmp = 8'h00;
    endcase
    out1 = tmp[0];
  end
endmodule
module m_fun_task(input logic [7:0] a, input logic [7:0] b, output logic [7:0] sum, output logic [7:0] diff);
  function logic [7:0] fhalf(input logic [7:0] v);
    return v >> 1;
  endfunction
  task tcompute(input logic [7:0] x, input logic [7:0] y, output logic [7:0] z);
    z = x + y;
  endtask
  always_comb begin
    sum = a + b;
    diff = a - b;
    sum = fhalf(sum);
    tcompute(a, b, sum);
  end
endmodule
module m_generate #(parameter int N = 4)(input logic [N-1:0] data_in, output logic [2*N-1:0] data_out);
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin : gen_loop
      assign data_out[2*i +: 2] = {data_in[i], data_in[i]};
    end
  endgenerate
endmodule
module m_pkg_import(input logic [3:0] x, input logic [3:0] y, output logic [3:0] z);
  import pkg_my::*;
  always_comb z = pkg_add(x, y);
endmodule
module m_class_usage(input logic clk, input logic reset, input logic [3:0] din, output logic [3:0] dout);
  C1 c_inst;
  logic [3:0] tmp;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      c_inst = new(0);
      dout <= 0;
    end else begin
      c_inst = new(din);
      tmp = c_inst.inc();
      dout <= tmp;
    end
  end
endmodule
module m_ifdef(input logic flag, input logic a, input logic b, output logic y);
  `ifdef USE_FLAG
    assign y = a & b;
  `else
    assign y = a | b;
  `endif
endmodule
module m_interface_usage(my_ifc.master IF, output logic ready);
  always_comb begin
    if (IF.valid) ready = 1'b1;
    else ready = 1'b0;
  end
endmodule
module m_dpi(input int a, input int b, output int sum);
  import "DPI-C" function int dpi_add(input int, input int);
  always_comb sum = dpi_add(a, b);
endmodule
module m_timeunits(input logic clk, input logic rst, output logic flag);
  timeunit 1ns;
  timeprecision 1ps;
  event ev;
  always_ff @(posedge clk) if (~rst) -> ev;
  always @(ev) flag = 1'b1;
endmodule
