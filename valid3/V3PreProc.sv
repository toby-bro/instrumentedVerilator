`timescale 1ns/1ps
module add_macro_mod(
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [8:0] sum
);
    `define ADD(a,b) ((a)+(b))
    assign sum = `ADD(a,b);
    `undef ADD
endmodule
module scale_mod(
    input  logic [15:0] din,
    output logic [15:0] dout
);
    `define SCALE(val, factor=2) ((val)*(factor))
    assign dout = `SCALE(din,4);
    `undef SCALE
endmodule
module string_join_mod(
    input  logic in_sig,
    output logic out_sig
);
    `define STR(s) `"s`"
    `define JOIN(a,b) a``b
    localparam string MODULE_NAME = `STR(string_join_mod);
    logic `JOIN(my,wire);
    assign `JOIN(my,wire) = in_sig;
    assign out_sig        = `JOIN(my,wire);
    `undef STR
    `undef JOIN
endmodule
module feature_width_mod(
    input  logic in_bus,
    output logic out_bus
);
    `define FEATURE_X
    `ifdef FEATURE_X
        assign out_bus = in_bus;
    `else
        assign out_bus = ~in_bus;
    `endif
    `undef FEATURE_X
endmodule
