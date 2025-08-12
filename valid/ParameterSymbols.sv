`timescale 1ns/1ps
virtual class base_class;
endclass
class child_class extends base_class;
    function new();
    endfunction
endclass
module param_chain #(
    parameter int X = 4,
    parameter int Y = X + 3,
    parameter int Z = Y * 2,
    parameter int VECTOR [0:1] = '{0:X, 1:Y}
) (
    input  logic [Z-1:0] in_data,
    output logic [Z-1:0] out_data
);
    assign out_data = in_data;
endmodule
module implicit_string_mod (
    input  logic i,
    output logic o
);
    parameter GREETING = "HELLO";
    localparam bit BIT0 = GREETING[0];
    assign o = i ^ BIT0;
endmodule
module type_param_mod #(
    parameter type T = child_class,
    parameter int  WIDTH = 8
) (
    input  logic [WIDTH-1:0] in_data,
    output logic [WIDTH-1:0] out_data
);
    T obj;
    initial begin
        obj = new();
    end
    assign out_data = in_data;
endmodule
module leaf #(
    parameter int W = 1
) (
    input  logic [W-1:0] a,
    output logic [W-1:0] y
);
    assign y = a;
endmodule
module defparam_mod (
    input  logic in_sig,
    output logic out_sig
);
    leaf inst (.a(in_sig), .y(out_sig));
    defparam inst.W = 1;
endmodule
module specparam_mod (
    input  wire a,
    input  wire b,
    input  wire c,
    output wire y
);
    specify
        specparam PATHPULSE$a$y = 10;
        specparam delay1 = 2;
        (a *> y) = delay1;
    endspecify
    assign y = a & b & c;
endmodule
module pattern_param_mod #(
    parameter int PACK [0:1] = '{0:1, 1:2}
) (
    input  logic [1:0] in_data,
    output logic [1:0] out_data
);
    assign out_data = in_data;
endmodule
