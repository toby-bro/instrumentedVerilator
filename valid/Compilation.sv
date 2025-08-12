timeunit 1ns / 1ps;
package util_pkg;
    typedef struct packed {logic [7:0] a; logic [7:0] b;} pair_t;
    typedef enum logic [1:0] {S0, S1, S2, S3} state_e;
    function automatic int max(input int lhs, input int rhs);
        max = (lhs > rhs) ? lhs : rhs;
    endfunction
endpackage
module net_demo(
    input  logic a,
    output logic y
);
    tri t;
    wire w;
    assign t = a;
    assign w = t;
    assign y = w;
endmodule
module generate_demo#(
    parameter int WIDTH = 8
)(
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : g
            assign out[i] = in[WIDTH-1-i];
        end
    endgenerate
endmodule
module attr_demo(
    input  logic i,
    output logic o
);
    (* unused, keep = "true" *) logic temp;
    assign temp = i;
    assign o    = temp;
endmodule
module dpi_demo(
    input  logic [31:0] in,
    output logic [31:0] out
);
    import "DPI-C" function int unsigned sv_add1(input int unsigned a);
    assign out = sv_add1(in);
endmodule
import util_pkg::*;
module package_use(
    input  logic [7:0] a,
    output logic [7:0] b
);
    pair_t p;
    always_comb begin
        p.a = a;
        p.b = ~a;
    end
    assign b = p.b;
endmodule
module time_demo(
    input  logic clk,
    output logic tick
);
    timeunit 1ns / 1ps;
    logic state;
    always_ff @(posedge clk) begin
        state <= ~state;
    end
    assign tick = state;
endmodule
import util_pkg::*;
module enum_demo(
    input  logic [1:0] s,
    output logic       y
);
    state_e current;
    always_comb begin
        current = state_e'(s);
        y       = (current == S3);
    end
endmodule
module supply_demo(
    input  logic dummy,
    output logic o
);
    supply0 gnd;
    supply1 vdd;
    assign o = vdd & ~gnd & dummy;
endmodule
module task_func_demo(
    input  logic a,
    output logic b
);
    function logic invert(input logic v);
        invert = ~v;
    endfunction
    assign b = invert(a);
endmodule
module gate_demo(
    input  wire a,
    input  wire b,
    output wire y
);
    and U1(y, a, b);
endmodule
