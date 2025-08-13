package my_pkg;
  parameter int WIDTH_P = 8;
  typedef logic [WIDTH_P-1:0] data_t;
  class my_class;
    data_t cdata;
    function new();
      cdata = '0;
    endfunction
  endclass
endpackage
interface simple_if #(parameter int DW = 8);
  logic                   clk;
  logic [DW-1:0]          data;
  modport master (input  clk, output data);
  modport slave  (input  clk, input  data);
endinterface
module leaf1(input  logic i,
             output logic o);
  assign o = i;
endmodule
module ds_user(input  logic i,
               output logic o);
  leaf1 u_leaf1 (.*);
endmodule
module rec_mod #(parameter int DEPTH = 1)
                (input  logic in,
                 output logic out);
  if (DEPTH == 0) begin : base
    assign out = in;
  end
  else begin : recur
    rec_mod #(.DEPTH(DEPTH-1)) u_rec (.in(in), .out(out));
  end
endmodule
module rec_parent #(parameter int DEPTH = 2)
                   (input  logic in,
                    output logic out);
  rec_mod #(.DEPTH(DEPTH)) u_rec (.in(in), .out(out));
endmodule
module producer #(parameter int DW = 8)
                 (simple_if.master bus,
                  input  logic               clk,
                  input  logic [DW-1:0]      din,
                  output logic [DW-1:0]      dout);
  assign dout     = din;
  assign bus.data = din;
endmodule
module consumer #(parameter int DW = 8)
                 (simple_if.slave bus,
                  input  logic              dummy_in,
                  output logic [DW-1:0]     d_out);
  assign d_out = bus.data;
endmodule
module intf_system #(parameter int DW = 8)
                    (input  logic              clk,
                     input  logic [DW-1:0]     din,
                     output logic [DW-1:0]     dout);
  simple_if #(DW) bus();
  logic [DW-1:0]  cons_dout;
  assign bus.clk = clk;
  producer  #(DW) prod_inst (.bus(bus), .clk(clk), .din(din),  .dout(dout));
  consumer  #(DW) cons_inst (.bus(bus), .dummy_in(1'b0), .d_out(cons_dout));
endmodule
module virt_user(simple_if.master bus,
                 input  logic in_sig,
                 output logic out_sig);
  assign out_sig = in_sig & bus.data[0];
endmodule
module virt_user_wrapper #(parameter int DW = 8)
                          (input  logic in_sig,
                           output logic out_sig);
  simple_if #(DW) ifc();
  virt_user u_vu (.bus(ifc), .in_sig(in_sig), .out_sig(out_sig));
endmodule
module pkg_user(input  my_pkg::data_t din,
                output my_pkg::data_t dout);
  assign dout = din;
endmodule
module class_user(input  logic clk,
                  input  logic rst_n,
                  input  logic in_sig,
                  output logic out_sig);
  import my_pkg::*;
  my_class obj;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      out_sig <= '0;
    end
    else begin
      if (obj == null) obj = new();
      out_sig <= in_sig;
    end
  end
endmodule
module binder_mod #(parameter int W = 8)
                  (input  logic [W-1:0] sig_in,
                   output logic [W-1:0] sig_out);
  always_comb sig_out = sig_in;
endmodule
bind class_user binder_mod #(.W(1)) bnd_i (.sig_in(in_sig), .sig_out());
