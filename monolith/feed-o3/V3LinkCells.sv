package my_pkg;
  parameter int P = 8;
  typedef logic [3:0] nibble_t;
  class packet_c;
    int len;
    function new();
      len = 0;
    endfunction
  endclass
endpackage
package pkg2;
  import my_pkg::*;
  export my_pkg::*;
endpackage
class base_c;
  bit flag;
endclass
class derived_c extends base_c;
  bit extra;
  function new();
    flag  = 0;
    extra = 0;
  endfunction
endclass
interface bus_if #(parameter int WIDTH = 8) (input logic clk);
  logic [WIDTH-1:0] data;
  logic             valid;
  modport master (output data, output valid);
  modport slave  (input  data, input  valid);
endinterface
module simple_inverter(input  logic in,
                       output logic out);
  assign out = ~in;
endmodule
module probe_pin(input  logic pin,
                 output logic pin_o);
  assign pin_o = pin;
endmodule
bind simple_inverter probe_pin pb (.pin(in), .pin_o());
module mod_use_pkg #(parameter int WIDTH = my_pkg::P)
                    (input  logic [WIDTH-1:0] din,
                     output logic [WIDTH-1:0] dout);
  import my_pkg::*;
  nibble_t   tmp;
  packet_c   pkt;
  derived_c  drv;
  always_comb begin
    tmp  = din[3:0];
    dout = { {(WIDTH-4){1'b0}}, tmp };
  end
  initial begin
    pkt = new();
    drv = new();
  end
endmodule
module iface_master(bus_if.master bus,
                    input  logic [bus.WIDTH-1:0] in_data,
                    input  logic                  in_valid,
                    output logic                  ready);
  assign bus.data  = in_data;
  assign bus.valid = in_valid;
  assign ready     = 1'b1;
endmodule
module iface_slave(bus_if.slave bus,
                   output logic [bus.WIDTH-1:0] out_data,
                   output logic                  out_valid,
                   input  logic                  ready);
  assign out_data  = bus.data;
  assign out_valid = bus.valid & ready;
endmodule
module parent_with_iface(input  logic clk,
                         input  logic [7:0] din,
                         input  logic       vin,
                         output logic [7:0] dout,
                         output logic       vout);
  bus_if #(.WIDTH(8)) bus_i (.clk(clk));
  iface_master m0 (.bus(bus_i), .in_data(din), .in_valid(vin), .ready());
  iface_slave  s0 (.bus(bus_i), .out_data(dout), .out_valid(vout), .ready(1'b1));
endmodule
module parent_star(input  logic in,
                   output logic out_port);
  logic out;
  logic o1;
  logic o2;
  simple_inverter u_named      (.in(in), .out(o1));
  simple_inverter u_positional (in, o2);
  simple_inverter u_star       (.*);
  assign out_port = o1 ^ o2 ^ out;
endmodule
module arr_if_mod(bus_if.slave bus,
                  input  logic dummy_in,
                  output logic [3:0] outvec);
  assign outvec = {4{bus.data[0]}};
endmodule
module vif_user(input logic clk,
                bus_if.slave bus_s,
                output logic [7:0] mirror_data);
  virtual bus_if.slave v_i;
  always_comb begin
    v_i         = bus_s;
    mirror_data = v_i.data;
  end
endmodule
module recurse_mod #(parameter int LEVEL = 0,
                      parameter int MAX   = 1)
                     (input  logic a,
                      output logic b);
  if (LEVEL < MAX) begin : gen_rec
    recurse_mod #(.LEVEL(LEVEL+1), .MAX(MAX)) next (.a(a), .b(b));
  end
  else begin : gen_last
    assign b = a;
  end
endmodule
module wrapper_hierarchy(input  logic        clk,
                         input  logic [7:0]  din,
                         input  logic        dummy_in,
                         output logic [7:0]  dout,
                         output logic [3:0]  collected);
  bus_if #(.WIDTH(8)) bus_main (.clk(clk));
  assign bus_main.data  = din;
  assign bus_main.valid = 1'b1;
  vif_user  u_vif (.clk(clk), .bus_s(bus_main.slave), .mirror_data(dout));
  arr_if_mod u_arr (.bus(bus_main.slave), .dummy_in(dummy_in), .outvec(collected));
endmodule
