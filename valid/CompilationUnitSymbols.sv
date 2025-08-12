timeunit 1ns / 1ps;
timeprecision 1ps;
package pkg1;
    parameter int P = 8;
endpackage
package export_pkg;
    import pkg1::*;
    export pkg1::*;
endpackage
interface ifc (input logic clk);
    logic data;
    modport master (input clk, output data);
    modport slave  (input clk, input  data);
endinterface
module simple_mod (
    input  logic in_sig,
    output logic out_sig
);
    assign out_sig = in_sig;
endmodule
module typeparam_mod #(
    parameter type T = logic,
    parameter int  W = 4
) (
    input  logic [W-1:0] in_bus,
    output T             out_bus
);
    assign out_bus = T'(in_bus[0]);
endmodule
module wildcard_mod #(
    parameter int W = 1
) (
    input  logic [W-1:0] in_sig,
    output logic [W-1:0] out_sig
);
    assign out_sig = in_sig;
endmodule
module nonansi_mod(in_a, out_a);
    input  logic in_a;
    output logic out_a;
    assign out_a = in_a;
endmodule
