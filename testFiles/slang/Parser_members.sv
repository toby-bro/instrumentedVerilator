timeunit 1ns / 1ps;
timeprecision 1ps;
package util_pkg;
    typedef enum logic [1:0] {
        S0 = 2'b00,
        S1 = 2'b01,
        S2 = 2'b10
    } state_e;
endpackage
interface simple_if (input logic clk);
    logic rst;
    modport master (input clk, rst);
endinterface
primitive up_and (out, in1, in2);
    output out;
    input  in1, in2;
    table
        0 0 : 0;
        0 1 : 0;
        1 0 : 0;
        1 1 : 1;
    endtable
endprimitive
module mod_timeunit (
    input  logic in_sig,
    output logic out_sig
);
    timeunit 1ns / 1ps;
    timeprecision 1ps;
    assign out_sig = in_sig;
endmodule
module mod_generate (
    input  logic [3:0] din,
    output logic [3:0] dout
);
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : g_block
            assign dout[i] = din[i];
        end
    endgenerate
endmodule
module mod_specify (
    input  wire sig_in,
    output wire sig_out
);
    assign sig_out = sig_in;
    specify
        (sig_in *> sig_out) = 1;
    endspecify
endmodule
module defparam_child #(
    parameter int WIDTH = 1
) (
    input  logic in,
    output logic out
);
    assign out = in;
endmodule
module mod_defparam (
    input  logic data_in,
    output logic data_out
);
    defparam u_dc.WIDTH = 4;
    defparam_child u_dc (
        .in (data_in),
        .out(data_out)
    );
endmodule
module simple_leaf (
    input  logic a,
    input  logic b,
    output logic y
);
    assign y = a & b;
endmodule
module mod_hierarchy (
    input  logic a,
    input  logic b,
    output logic y
);
    simple_leaf u_leaf (
        .a(a),
        .b(b),
        .y(y)
    );
endmodule
