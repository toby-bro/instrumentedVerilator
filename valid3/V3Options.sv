`timescale 1ns/1ps
package pkg_defs;
  typedef struct packed {logic [3:0] a; logic [3:0] b;} my_struct_t;
endpackage
interface bus_if #(parameter WIDTH = 8) (input logic clk);
  timeunit      1ns;
  timeprecision 1ps;
  logic [WIDTH-1:0] data;
  modport master (input clk, output data);
  modport slave  (input clk, input  data);
endinterface
module timescale_mod #(parameter W = 8)
  (input  logic                 clk,
   input  logic [W-1:0]         in,
   output logic [W-1:0]         out);
  timeunit      1ns;
  timeprecision 1ps;
  always_ff @(posedge clk) out <= in;
  always_ff @(posedge clk) assert(out == in);
endmodule
module feature_generate #(parameter WIDTH = 8, parameter GEN = 1)
  (input  logic [WIDTH-1:0] a,
   output logic [WIDTH-1:0] y);
  timeunit      1ns;
  timeprecision 1ps;
  if (GEN) begin : g1
      assign y = a;
  end else begin : g0
      assign y = {WIDTH{1'b0}};
  end
endmodule
module feature_unique
  (input  logic [1:0] sel,
   output logic       out);
  timeunit      1ns;
  timeprecision 1ps;
  always_comb begin
      unique case (sel)
         2'd0: out = 1'b0;
         2'd1: out = 1'b1;
         default: out = 1'b0;
      endcase
  end
endmodule
module feature_assert
  (input logic clk,
   input logic req,
   input logic gnt,
   output logic ok);
  timeunit      1ns;
  timeprecision 1ps;
  assign ok = gnt;
  property grant_delayed; @(posedge clk) req |=> gnt; endproperty
  assert property(grant_delayed);
endmodule
module feature_simple #(parameter W = 4)
  (input  logic [W-1:0] sig_in,
   output logic [W-1:0] sig_out);
  timeunit      1ns;
  timeprecision 1ps;
  assign sig_out = ~sig_in;
endmodule
module feature_enum
  (input  logic [1:0] cmd,
   output logic       act);
  timeunit      1ns;
  timeprecision 1ps;
  typedef enum logic [1:0] {IDLE = 2'd0, RUN = 2'd1, STOP = 2'd2, ERR = 2'd3} state_e;
  state_e state;
  function automatic logic check(input state_e s);
     check = (s == RUN);
  endfunction
  always_comb begin
     state = state_e'(cmd);
     act   = check(state);
  end
endmodule
module feature_struct #(parameter W = 4)
  (input  logic [W-1:0] a,
   output logic [W-1:0] b);
  timeunit      1ns;
  timeprecision 1ps;
  typedef struct packed {logic [W-1:0] x; logic [W-1:0] y;} pair_t;
  pair_t p;
  always_comb begin
     p.x = a;
     p.y = ~a;
     b   = p.x & ~p.y;
  end
endmodule
module feature_class
  (input  logic       clk,
   input  logic [7:0] din,
   output logic [7:0] dout);
  timeunit      1ns;
  timeprecision 1ps;
   class filter_c;
      bit [7:0] last;
      function new(); last = 0; endfunction
      function bit [7:0] pass(bit [7:0] v);
         last = v;
         return last;
      endfunction
   endclass
   filter_c f = new();
   always_ff @(posedge clk) begin
      dout <= f.pass(din);
   end
endmodule
module feature_inside
  (input  logic signed [3:0] value,
   output logic              hit);
  timeunit      1ns;
  timeprecision 1ps;
  always_comb hit = (value inside {[-3:3]});
endmodule
module feature_array #(parameter N = 4)
  (input  logic [N-1:0] in,
   output logic [N-1:0] out);
  timeunit      1ns;
  timeprecision 1ps;
  generate
     genvar i;
     for (i = 0; i < N; i++) begin : gen
        assign out[i] = in[i] ^ 1'b1;
     end
  endgenerate
endmodule
`define MY_MACRO(x) ((x) + 1)
module feature_macro
  (input  logic [3:0] in,
   output logic [3:0] out);
  timeunit      1ns;
  timeprecision 1ps;
  assign out = `MY_MACRO(in);
endmodule
module interface_user
  (input  logic        clk,
   input  logic [7:0]  in,
   output logic [7:0]  out,
   bus_if.master       vif);
  timeunit      1ns;
  timeprecision 1ps;
  import pkg_defs::*;
  assign out = in;
  always_comb vif.data = in;
endmodule
