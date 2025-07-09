package common_pkg;
   typedef logic [7:0] byte_t;
   parameter int MY_PARAM = 32;
endpackage
package mypkg;
   parameter int P = 1;
   function int inc (int i); inc = i + 1; endfunction
endpackage
interface bus_if #(parameter WIDTH = 8) ();
   logic [WIDTH-1:0] data;
   modport master (output data);
   modport slave  (input  data);
endinterface
primitive my_udp (o, i);
   output o;
   input  i;
   table
      0 : 0;
      1 : 1;
   endtable
endprimitive
module generate_example #(parameter WIDTH = 8)
   (input  logic                     clk,
    input  logic                     en,
    input  logic [WIDTH-1:0]         in,
    output logic [WIDTH-1:0]         out);
   import common_pkg::*;
   logic [WIDTH-1:0] in_reg;
   always_ff @(posedge clk) begin
      if (en) in_reg <= in;
   end
   /*--------------------------------------------------------------------
    * If / Case / Loop generate constructs
    *------------------------------------------------------------------*/
   logic [WIDTH-1:0] out_if;
   logic [WIDTH-1:0] out_case;
   genvar i;
   generate
      if (WIDTH == 8) begin : gen_if_block
         assign out_if = in_reg;
      end
      else begin : gen_else_block
         assign out_if = {WIDTH{1'b0}};
      end
   endgenerate
   generate
      case (WIDTH)
         1 : begin : gen_case1
            assign out_case = {WIDTH{in_reg[0]}};
         end
         8 : begin : gen_case8
            assign out_case = in_reg;
         end
         default : begin : gen_case_default
            assign out_case = {WIDTH{1'b0}};
         end
      endcase
   endgenerate
   generate
      for (i = 0; i < WIDTH; i = i + 1) begin : gen_loop
         wire bit_i;
         assign bit_i = in_reg[i];
      end
   endgenerate
   assign out = out_if ^ out_case;
endmodule
module enum_typedef_module
   (input  logic [1:0] sel,
    output logic       y);
   typedef enum logic [1:0] {
      S0 = 2'b00,
      S1 = 2'b01,
      S2 = 2'b10
   } state_e;
   state_e state;
   /* forward typedef and alias */
   typedef struct packed {
      logic a;
   } my_struct_t;
   typedef my_struct_t fwd_struct_t;
   always_comb begin
      case (sel)
         2'd0 : state = S0;
         2'd1 : state = S1;
         default : state = S2;
      endcase
      y = (state == S1);
   end
endmodule
module specify_module
   (input  wire a,
    input  wire b,
    output wire y);
   specify
      (a *> y) = (1,1);
      (b *> y) = (1,1);
   endspecify
   assign y = a & b;
endmodule
module sequential_module
   (input  logic clk,
    input  logic rst,
    input  logic d,
    output logic q);
   /* FF style */
   always_ff @(posedge clk or posedge rst) begin
      if (rst) q <= 1'b0;
      else     q <= d;
   end
   /* Latch style (separate signal to avoid multiple drivers) */
   logic latch_q;
   always_latch begin
      if (!clk) latch_q = d;
   end
   function logic invert (logic i);
      invert = ~i;
   endfunction
endmodule
module nonansi_module (a, b, y);
   input  logic a;
   input  logic b;
   output logic y;
   wire w;
   assign w = a ^ b;
   assign y = w;
endmodule
module param_module #(parameter int WIDTH = 8)
   (input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out);
   localparam int DEPTH = 16;
   parameter type T = logic [WIDTH-1:0];
   assign out = in;
endmodule
module pkg_user
   (input  logic a,
    output logic b);
   import mypkg::*;
   assign b = (inc(P) == 2) ? a : ~a;
endmodule
