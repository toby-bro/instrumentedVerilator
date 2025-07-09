`timescale 1ns/1ps
`define MY_STR "Hello, SystemVerilog!"
`define HEX32 32'hDEADBEEF
`define BIG_HEX 128'h0123456789ABCDEF_FEDCBA9876543210
`define REAL_PI 3.1415926535
`define TEN_NS 10ns
`define UNBASED_ONE '1
`define UNBASED_X   'x
`define UNBASED_Z   'z
`define MY_AND(a,b) ((a) & (b))
`define MULT_MACRO(a,b,c) ((a) ? (b):(c))
module numeric_literals_mod (
    input  logic [127:0] in_data,
    output logic [127:0] out_data
);
    localparam logic [127:0] CONST_HEX = `BIG_HEX;
    assign out_data = in_data ^ CONST_HEX;
endmodule
module real_time_mod (
    input  logic clk,
    output logic [63:0] t_out
);
    always_ff @(posedge clk) begin
        t_out <= `TEN_NS;
    end
endmodule
module unbased_literal_mod (
    input  logic dummy,
    output logic val_x
);
    assign val_x = `UNBASED_X;
endmodule
module string_literal_mod (
    input  logic [7:0] idx,
    output logic [7:0] char_out
);
    localparam string MSG = `MY_STR;
    assign char_out = idx[0] ? 8'd65 : 8'd66;
endmodule
module escaped_identifier_mod (
    input  logic in_sig,
    output logic out_sig
);
    wire \with_esc_id ;
    assign \with_esc_id  = in_sig;
    assign out_sig       = \with_esc_id ;
endmodule
module macro_cond_mod (
    input  logic [31:0] in_a,
    output logic [31:0] out_b
);
`ifndef SOME_UNDEFINED_SYMBOL
    localparam int VAL = `HEX32;
`else
    localparam int VAL = 32'd0;
`endif
    assign out_b = in_a ^ VAL;
endmodule
module system_identifier_mod (
    input  logic [7:0] vec,
    output integer     result
);
    assign result = $bits(vec);
endmodule
module integer_base_signed_mod (
    input  logic  [3:0] in_data,
    output integer      out_val
);
    localparam integer DEC_VAL = -32'sd42;
    assign out_val = DEC_VAL + in_data;
endmodule
module class_inst_mod (
    input  logic clk,
    output logic [7:0] o
);
    class Simple;
        rand bit [7:0] x;
        function new(bit [7:0] val);
            x = val;
        endfunction
    endclass
    logic [7:0] tmp;
    always_ff @(posedge clk) begin : blk
        Simple s;
        s = new(8'hAA);
        tmp <= s.x;
    end
    assign o = tmp;
endmodule
module integer_big_mod (
    input  logic [255:0] in_d,
    output logic [255:0] out_d
);
    localparam logic [255:0] BIG = 256'hFFFFFFFFFFFFFFFF_FFFFFFFFFFFFFFFF_FFFFFFFFFFFFFFFF_FFFFFFFFFFFFFFFF;
    assign out_d = in_d | BIG;
endmodule
module line_continuation_mod (
    input  logic a,
    output logic b
);
`define AND3(a,b,c) \
    ((a) & (b) & (c))
    assign b = `AND3(a, 1'b1, 1'b1);
`undef AND3
endmodule
`default_nettype none
module no_nettype_mod (
    input  logic x,
    output logic y
);
    assign y = x;
endmodule
`default_nettype wire
