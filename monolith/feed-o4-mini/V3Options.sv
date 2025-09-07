`timescale 1ns/1ps
module timescale_mod(input logic clk, input logic rst, output logic out);
   assign out = clk & rst;
endmodule
(* hierarchical_block="orig,mangled,param0,val0,param1,val1" *)
module hier_block_mod(input logic a, output logic b);
   assign b = a;
endmodule
import "DPI-C" function int foo_dpi(input int x);
module dpi_mod(input logic [3:0] in, output logic [3:0] out);
   assign out = foo_dpi(in);
endmodule
module gen_mod(input  logic       sel,
               input  logic [3:0] din,
               output logic [3:0] dout);
   genvar i;
   generate
      for (i = 0; i < 4; i++) begin : genblk
         if (i < 2) begin
            assign dout[i] = din[i] & sel;
         end else begin
            assign dout[i] = din[i] | sel;
         end
      end
   endgenerate
endmodule
class MyClass;
   function int inc(input int v);
      return v + 1;
   endfunction
endclass
module class_mod(input  logic [7:0] in, output logic [7:0] out);
   always_comb begin
      static MyClass c = new();
      out = c.inc(in);
   end
endmodule
interface my_if(input logic clk);
   logic sig;
   modport master(output sig);
   modport slave (input  sig);
endinterface
module iface_mod(input logic clk, output logic sig_o);
   my_if intf(.clk(clk));
   assign sig_o = intf.sig;
endmodule
package pkg_mod;
   typedef struct packed { logic a; logic b; } my_struct_t;
endpackage
module pkg_user(input  pkg_mod::my_struct_t s, output logic y);
   assign y = s.a ^ s.b;
endmodule
module cover_mod(input logic clk, input logic d, output logic q);
   logic q_reg;
   always_ff @(posedge clk) begin
      if (d) q_reg <= !q_reg;
   end
   assign q = q_reg;
   covergroup cg @(posedge clk);
      coverpoint d;
   endgroup
   cg cg_inst = new();
endmodule
(* protect_ids, protect_key="KEY123" *)
module protect_mod(input logic p, output logic r);
   assign r = ~p;
endmodule
`define CONST_VAL 8'hFF
module macro_mod(input  logic [7:0] din,
                 output logic [7:0] dout);
   `ifdef CONST_VAL
      localparam logic [7:0] LV = `CONST_VAL;
   `else
      localparam logic [7:0] LV = 8'h00;
   `endif
   assign dout = din ^ LV;
endmodule
module defparam_child #(parameter int P = 1)
                       (input  logic x, output logic y);
   assign y = x * P;
endmodule
module defparam_mod(input logic in, output logic out);
   defparam_child #(.P(2)) defparam_child_inst(.x(in), .y(out));
   defparam defparam_child_inst.P = 5;
endmodule
