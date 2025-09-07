`define STRIFY(x) `"x`"
`define CONCAT(a,b) a``b
`define IDENTITY(x) x
`define ADD(a,b=8) ((a)+(b))
`define MAKE_WIRE(name,width) logic [(width)-1:0] `CONCAT(name,_bus);
`define MACRO_LF a + b \
                 + c
`line 100 "generated_code.sv" 0
`pragma protect begin_protected
`pragma protect key_keyowner = "VerilatorUser"
`pragma protect key_method  = "rsa"
`pragma protect key_block
MIIA==
`pragma protect encoding = (enctype = "base64", line_length = 76, bytes = 4)
QUJDRA==
`pragma protect end_protected
and more text
/* Block comment containing a backslash \
still within comment */
/***************************************************************************
 * Module exercising token concatenation through `CONCAT
 ***************************************************************************/
module concat_demo #(parameter WIDTH = 8)
(
    input   logic [WIDTH-1:0]  in_sig,
    output  logic [WIDTH-1:0]  out_sig
);
    `MAKE_WIRE(my, WIDTH)
    always_comb begin
        `CONCAT(my,_bus) = in_sig;
        out_sig          = `CONCAT(my,_bus);
    end
endmodule
/***************************************************************************
 * Module exercising stringify operator
 ***************************************************************************/
module stringify_demo #(parameter WIDTH = 4)
(
    input  logic [WIDTH-1:0]  a,
    output logic [WIDTH-1:0]  y
);
    localparam string NAME_STR = `STRIFY(stringify_demo);
    assign y = a;  
endmodule
/***************************************************************************
 * Module exercising default arguments and arithmetic in macros
 ***************************************************************************/
module default_arg_demo #(parameter W = 16)
(
    input  logic [W-1:0]  din,
    output logic [W-1:0]  dout
);
    localparam int CALC = `ADD(5);
    assign dout = din + CALC;
endmodule
/***************************************************************************
 * Module exercising conditional compilation
 ***************************************************************************/
`define FEATURE_ON
module ifdef_demo
(
    input  logic clk,
    input  logic rst_n,
    output logic active
);
`ifdef FEATURE_ON
    assign active = clk & rst_n;
`else
    assign active = 1'b0;
`endif
endmodule
/***************************************************************************
 * Module demonstrating class instantiation inside procedural block
 ***************************************************************************/
class dummy_c;
    function int id(); return 1; endfunction
endclass
module class_proc_demo (input logic in_bit, output logic out_bit);
    always_comb begin
        dummy_c d = new();
        out_bit = in_bit & (d.id() == 1);
    end
endmodule
