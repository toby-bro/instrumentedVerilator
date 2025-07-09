timeunit 1ns;
timeprecision 100ps;
package math_pkg;
   typedef logic [31:0] word_t;
   function automatic int add (int a, int b);
      add = a + b;
   endfunction
endpackage
package sub_pkg;
   typedef logic [15:0] half_t;
endpackage
class helper_c;
   int value;
   function new (int v);
      value = v;
   endfunction
endclass
interface bus_if #(parameter int W = 8);
   logic clk;
   logic [W-1:0] data;
   modport master (input clk, output data);
   modport slave  (output clk, input data);
endinterface
module timescale_mod #(parameter int DELAY = 1) (
   input  logic in,
   output logic out
);
   timeunit 1ns;
   timeprecision 1ps;
   always_comb begin
      helper_c h;
      h = new(DELAY);
      out = in;
   end
endmodule
module param_type_mod #(
   parameter int  WIDTH = 8,
   localparam int DOUBLE_WIDTH = WIDTH * 2,
   type T = logic [WIDTH-1:0]
) (
   input  logic clk,
   input  T     din,
   output T     dout
);
   T internal;
   always_ff @(posedge clk) begin
      internal <= din;
   end
   assign dout = internal;
endmodule
module nonansi (clk, rst_n, data_in, data_out);
   input  logic        clk;
   input  logic        rst_n;
   input  logic [7:0]  data_in;
   output logic [7:0]  data_out;
   localparam logic [7:0] CONSTANT = 8'hAA;
   always_ff @(posedge clk) begin
      if (!rst_n)
         data_out <= '0;
      else
         data_out <= data_in ^ CONSTANT;
   end
endmodule
module wild_mod (
   input  logic in_w,
   output logic out_w
);
   always_comb out_w = in_w;
endmodule
module pkg_user (
   input  math_pkg::word_t a,
   input  math_pkg::word_t b,
   output math_pkg::word_t c
);
   import math_pkg::add;
   always_comb begin
      c = add(a, b);
   end
endmodule
module iface_consumer (
   input  logic       enable,
   input  logic [7:0] in_bus_data,
   output logic [7:0] data_out
);
   typedef virtual bus_if.master v_if_t;
   v_if_t vif;
   always_comb begin
      data_out = enable ? in_bus_data : '0;
   end
endmodule
