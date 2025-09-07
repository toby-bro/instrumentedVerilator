package pkg_types;
  typedef struct packed { int a; bit b; } mystruct_t;
endpackage
package pkg_utils;
  function automatic int mult(input int x, input int y);
    mult = x * y;
  endfunction
endpackage
`default_nettype none
module mod_line(input logic clk, input logic rst, output logic out);
`line 42 "mod_line.sv" 1
  assign out = clk & rst;
endmodule
module mod_macros(input logic a, input logic b, output logic y);
`define HIGH
`ifdef HIGH
  assign y = a & b;
`else
  assign y = a | b;
`endif
`undef HIGH
endmodule
module mod_generate #(parameter WIDTH = 8)(input logic [WIDTH-1:0] din, output logic [WIDTH-1:0] dout);
  generate
    genvar i;
    for (i = 0; i < WIDTH; i = i + 1) begin : genblock
      assign dout[i] = din[i];
    end
    if (WIDTH > 4) begin : wide
      assign dout = din;
    end
  endgenerate
endmodule
module mod_func(input logic [3:0] a, output logic [3:0] b);
  function automatic logic [3:0] incr(input logic [3:0] x);
    incr = x + 1;
  endfunction
  assign b = incr(a);
endmodule
module mod_task(input logic [7:0] a, output logic [7:0] b);
  task automatic invert(input logic [7:0] in, output logic [7:0] out);
    out = ~in;
  endtask
  always_comb invert(a, b);
endmodule
class calc;
  function int add(input int x, input int y);
    return x + y;
  endfunction
endclass
module mod_class(input logic [3:0] a, input logic [3:0] b, output logic [7:0] sum);
  always_comb begin
    calc c = new;
    sum = c.add(a, b);
  end
endmodule
interface intf_if(input logic clk);
  logic sig;
  modport mp (input clk, output sig);
endinterface
module mod_intf(intf_if.mp iface);
endmodule
module mod_array(input logic [1:0][3:0] arr_in, output logic [1:0][3:0] arr_out);
  assign arr_out = arr_in;
endmodule
module mod_struct(input logic clk, input logic [7:0] din, output logic [7:0] dout);
  typedef union packed {
    logic [7:0] u8;
    struct packed { logic [3:0] hi; logic [3:0] lo; } parts;
  } data_u;
  data_u du;
  always_ff @(posedge clk) begin
    du.u8 <= din;
    du.parts.hi <= du.parts.hi + 1;
  end
  assign dout = du.u8;
endmodule
module mod_enum(input logic en, output logic [1:0] state_out);
  typedef enum logic [1:0] { S0 = 2'b00, S1 = 2'b01, S2 = 2'b10 } state_t;
  state_t state;
  always_comb begin
    if (en) state = S1;
    else state = S0;
    state_out = state;
  end
endmodule
module mod_assert(input logic clk, input logic [3:0] sig);
  always @(posedge clk) assert (sig != 4'hF);
endmodule
module mod_pkgimport(input logic [31:0] x, output logic [31:0] y);
  import pkg_types::*;
  mystruct_t ms;
  always_comb begin
    ms.a = x;
    ms.b = 1;
    y = ms.a;
  end
endmodule
`default_nettype wire
