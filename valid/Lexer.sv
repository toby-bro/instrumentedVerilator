`timescale 1ns/1ps
`define INTVAL       32'd123
`define MAKE_STR(s)  `"s`"
`define PASTE(a,b)   a``b
module basic_ops (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] y
);
    assign y = (a !== b) ? {8{~&a}} : ((a ==? b) ? a : b);
endmodule
module number_literals (
    input  logic        dummy_in,
    output logic [31:0] y
);
    localparam int     DEC    = 123456789;
    localparam int     OCT    = 32'o1234567;
    localparam int     HEX    = 32'hDEAD_BEEF;
    localparam int     BIN    = 8'b1010_1100;
    localparam int     SDNUM  = 16'sd42;
    localparam logic   U1     = '1;
    localparam logic   UX     = 'x;
    localparam logic   UZ     = 'z;
    localparam real    PI     = 3.14e0;
    localparam time    DELAY  = 5ms;
    assign y = HEX ^ BIN ^ DEC ^ SDNUM;
endmodule
module slice_pluscolon (
    input  logic [15:0] a,
    output logic [7:0]  hi,
    output logic [7:0]  lo
);
    assign hi = a[8  +: 8];
    assign lo = a[15 -: 8];
endmodule
module streaming_rep (
    input  logic [15:0] vec_in,
    output logic [15:0] vec_out
);
    assign vec_out = {<<{vec_in}};
endmodule
module shifts (
    input  logic [31:0] data,
    input  logic [4:0]  shamt,
    output logic [31:0] y
);
    assign y = ((data << shamt) <<< shamt) ^ ((data >> shamt) >>> shamt);
endmodule
module assertion_seq (
    input  logic clk,
    input  logic rst_n,
    input  logic a,
    input  logic b,
    output logic dummy
);
    property p1;
        @(posedge clk) disable iff (!rst_n) a ##1 b;
    endproperty
    assert property (p1);
    assign dummy = a;
endmodule
module macro_usage (
    input  logic [31:0] in_val,
    output logic [95:0] out_str
);
    localparam int    V  = `INTVAL;
    localparam logic [95:0] S  = `MAKE_STR(hello_world);
    localparam int    J  = `PASTE(12,34);
    always_comb begin
        out_str = S;
    end
endmodule
module escape_ident (
    input  logic dummy_in,
    output logic dummy_out
);
    wire \with$symbol  = dummy_in ;
    assign dummy_out = \with$symbol ;
endmodule
