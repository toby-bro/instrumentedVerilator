package pkg_colors;
  typedef enum logic [1:0] { RED=2'b00, GREEN=2'b01, BLUE=2'b10 } color_e;
endpackage: pkg_colors
package pkg_types;
  typedef logic [7:0] byte_t;
endpackage: pkg_types
interface simple_if(input logic clk);
  logic sig;
  modport master (input sig, output clk);
  modport slave  (output sig, input clk);
endinterface: simple_if
module simple_mod(input  logic in, output logic out);
  assign out = in;
endmodule: simple_mod
module param_mod#(parameter int WIDTH = 8)
  (input  logic [WIDTH-1:0] inbus,
   output logic [WIDTH-1:0] outbus);
  assign outbus = inbus;
endmodule: param_mod
module defparam_use(input logic t, output logic s);
  param_mod #(.WIDTH(4)) u1(.inbus(t), .outbus(s));
  defparam u1.WIDTH = 2;
endmodule: defparam_use
module nested_gen(input  logic enable,
                  input  logic [3:0] in,
                  output logic [3:0] out);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : genblk
      assign out[i] = enable ? in[i] : 1'b0;
    end
  endgenerate
endmodule: nested_gen
module gen_if(input  logic sel,
              input  logic d0,
              input  logic d1,
              output logic y);
  always_comb begin
    if (sel)
      y = d1;
    else
      y = d0;
  end
endmodule: gen_if
module inner_mod(input  logic a, output logic b);
  assign b = ~a;
endmodule: inner_mod
module outer_mod(input  logic a,
                 input  logic c,
                 output logic b,
                 output logic d);
  inner_mod u_inner1(.a(a), .b(b));
  inner_mod u_inner2(.a(c), .b(d));
endmodule: outer_mod
module typedef_mod(input  logic a, output logic b);
  typedef logic [3:0] nibble_t;
  nibble_t t;
  assign t = a ? 4'b1010 : 4'b0101;
  assign b = t[0];
endmodule: typedef_mod
module pkg_import_user(input  logic sel,
                       output pkg_colors::color_e color);
  import pkg_colors::*;
  assign color = sel ? GREEN : BLUE;
endmodule: pkg_import_user
import "DPI-C" function int dpi_func(input int x);
module dpi_user(input int x, output int y);
  assign y = dpi_func(x);
endmodule: dpi_user
module ptype_mod#(type T = int)
  (input  T val, output T out);
  assign out = val;
endmodule: ptype_mod
module ptype_use(input  logic [3:0] a,
                 output logic [3:0] b);
  ptype_mod#(.T(logic [3:0])) pu(.val(a), .out(b));
endmodule: ptype_use
module func_task_mod(input  logic clk,
                     input  logic rst,
                     input  logic d,
                     output logic q,
                     output logic done);
  function automatic logic myfunc(input logic in_d, input logic in_en);
    myfunc = in_en ? ~in_d : in_d;
  endfunction
  task automatic mytask(output logic out_done);
    out_done = clk & rst;
  endtask
  assign q = myfunc(d, clk);
  always_comb begin
    mytask(done);
  end
endmodule: func_task_mod
module foreach_mod(input  logic [3:0] arr_in,
                   output logic [3:0] arr_out);
  integer i;
  always_comb begin
    foreach (arr_in[i])
      arr_out[i] = arr_in[i];
  end
endmodule: foreach_mod
module iface_user(input  logic clk,
                  input  logic data,
                  output logic sig_out,
                  output logic resp);
  simple_if intf_inst(.clk(clk));
  assign sig_out = intf_inst.sig;
  assign resp    = clk & intf_inst.sig;
endmodule: iface_user
