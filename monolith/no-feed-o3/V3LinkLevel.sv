package TypesPkg;
    typedef struct packed {
        logic [3:0] a;
        logic [3:0] b;
    } pair_t;
endpackage
interface Iface #(parameter WIDTH = 8) (input logic clk);
    logic [WIDTH-1:0] data;
    modport master (input  data);
    modport slave  (output data);
endinterface
module Alpha #(parameter WIDTH = 8) (
    input  logic clk,
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    timeunit 1ns/1ps;
    assign out = in;
endmodule
module Beta #(parameter WIDTH = 4) (
    input  logic clk,
    input  logic [WIDTH-1:0] in2,
    Iface.master bus,
    output logic [WIDTH-1:0] out2
);
    assign out2 = in2;
endmodule
module Gamma #(parameter WIDTH = 8) (
    input  logic clk,
    Iface.slave if_arr [2],
    output logic [WIDTH-1:0] out_arr
);
    assign out_arr = if_arr[0].data;
endmodule
module Delta (
    input  logic clk,
    input  TypesPkg::pair_t in_pair,
    output TypesPkg::pair_t out_pair
);
    timeunit 10ns/1ns;
    assign out_pair = in_pair;
endmodule
module RefMod (
    input  logic dummy,
    ref    logic [7:0] value,
    output logic [7:0] out
);
    assign out = value;
endmodule
module ConstRefMod (
    input      logic dummy,
    const ref  logic [7:0] c_value,
    output     logic [7:0] out
);
    assign out = c_value;
endmodule
