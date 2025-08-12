package util_pkg;
  typedef struct packed {logic [7:0] data;} t_data_s;
  class rand_class;
    rand bit [7:0] r;
    constraint c_r { r inside {[0:255]}; }
    function new(); endfunction
    function bit [7:0] get(); return r; endfunction
  endclass
endpackage
interface bus_if (input logic clk);
    logic [7:0] data;
    modport master (input clk, output data);
    modport slave  (input clk, input  data);
endinterface
primitive nand_udp (Y, A, B);
    output Y; input A, B;
    table
        0 0 : 1;
        0 1 : 1;
        1 0 : 1;
        1 1 : 0;
        ? x : 1;
        x ? : 1;
    endtable
endprimitive
module mod_child (input  logic a,
                  input  logic b,
                  output logic y);
    nand_udp u0 (y, a, b);
endmodule
module mod_gen #(parameter WIDTH = 4)
                (input  logic [WIDTH-1:0] in,
                 output logic [WIDTH-1:0] out);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : bit_gen
            if (i % 2 == 0) begin : even_blk
                assign out[i] =  in[i];
            end else begin : odd_blk
                assign out[i] = ~in[i];
            end
        end
    endgenerate
endmodule
module ifc_master (input  logic       clk,
                   input  logic [7:0] d_in,
                   output logic [7:0] d_out);
    bus_if bus_i (.clk(clk));
    assign bus_i.data = d_in;
    assign d_out      = bus_i.data;
endmodule
module ifc_slave (input  logic       clk,
                  input  logic [7:0] d_in,
                  output logic [7:0] d_out);
    bus_if bus_i (.clk(clk));
    assign d_out = bus_i.data;
endmodule
module class_user (input  logic       clk,
                   output logic [7:0] rand_val);
    import util_pkg::*;
    rand_class rc;
    always_comb rand_val = (rc == null) ? '0 : rc.get();
    initial begin
        rc = new();
    end
endmodule
package math_pkg;
    function automatic logic parity(input logic [7:0] v);
        parity = ^v;
    endfunction
endpackage
module pkg_user (input  logic [7:0] in,
                 output logic       out);
    import math_pkg::*;
    assign out = parity(in);
endmodule
module hierarchy_parent (input  logic [3:0] bus_in,
                         output logic [3:0] bus_out);
    mod_gen #(.WIDTH(4)) u_gen (.in(bus_in), .out(bus_out));
endmodule
