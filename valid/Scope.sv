package utils_pkg;
  typedef logic [31:0] word_t;
  function automatic word_t and2(word_t a, word_t b);
    and2 = a & b;
  endfunction
endpackage
package mypkg;
  parameter int P = 42;
  function automatic int addP(input int x);
    addP = x + P;
  endfunction
endpackage
interface bus_if;
  logic        clk;
  logic [7:0]  data;
  modport master (input  clk, output data);
  modport slave  (output clk, input  data);
endinterface
module generate_mod #(parameter int WIDTH = 8)
  (input  logic [WIDTH-1:0] a,
   output logic [WIDTH-1:0] y);
  import utils_pkg::*;
  wire [WIDTH-1:0] y_if;
  wire [WIDTH-1:0] y_case;
  if (WIDTH == 8) begin : g_equal
    assign y_if = a;
  end
  else begin : g_other
    assign y_if = {WIDTH{1'b0}};
  end
  generate
    case (WIDTH)
      8: begin : c8
        assign y_case = a;
      end
      default: begin : cdef
        assign y_case = {WIDTH{1'b1}};
      end
    endcase
  endgenerate
  generate
    genvar i;
    for (i = 0; i < WIDTH; i++) begin : g_loop
      wire tmp;
      assign tmp = a[i];
    end
  endgenerate
  assign y = y_if ^ y_case;
endmodule
module nonansi_iface_port_mod (clk, data_o);
  input  logic       clk;
  output logic [7:0] data_o;
  import utils_pkg::*;
  bus_if intf();
  assign intf.clk  = clk;
  assign intf.data = 8'hAA;
  assign data_o    = intf.data;
endmodule
module nested_def_mod #(parameter int W = 8)
  (input  logic [W-1:0] din,
   output logic [W-1:0] dout);
  import mypkg::*;
  module inner #(parameter int IW = W)
    (input  logic [IW-1:0] i,
     output logic [IW-1:0] o);
    assign o = i;
  endmodule
  inner u_inner (.i(din), .o(dout));
  if (W == 8) begin : g_fixed
    typedef logic [W-1:0] vec_t;
    vec_t tmp;
    assign tmp = din;
  end
endmodule
module primitive_example_mod
  (input  logic a,
   input  logic b,
   output logic y);
  wire y_net;
  and and_gate (y_net, a, b);
  assign y = y_net;
endmodule
module enum_mod
  (input  logic sig_i,
   output logic sig_o);
  typedef enum logic [1:0] {
    S_IDLE = 2'b00,
    S_RUN  = 2'b01,
    S_STOP = 2'b10
  } state_e;
  state_e current_state;
  assign sig_o = (current_state == S_IDLE) ? sig_i : ~sig_i;
endmodule
module port_declaration_mod (clk, rst_n, out_p);
  input  logic clk;
  input  logic rst_n;
  output logic out_p;
  logic internal;
  assign internal = clk & rst_n;
  assign out_p    = internal;
endmodule
module task_mod
 (input  logic a_i,
  output logic b_o);
  task automatic pass_through(input logic x, output logic y);
    y = x;
  endtask
  always_comb begin
    pass_through(a_i, b_o);
  end
endmodule
