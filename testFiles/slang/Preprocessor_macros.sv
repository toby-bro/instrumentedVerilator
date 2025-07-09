`define ADD(a, b) ((a)+(b))
`define CONCAT(a, b) a``b
`define STR(x) `"x`"
`define MULT(a, b=2) ((a)*(b))
`define FOO(bar) `bar
`define CALL_ADD2(x) `ADD(x, 2)
`define ESC_ID(name) \name``_id
`define ONE_LOCAL 1
module add_macro_mod (
    input  logic [31:0] in,
    output logic [31:0] out
);
    assign out = `ADD(in, 1);
endmodule
module concat_macro_mod (
    input  logic        dummy,
    output logic [31:0] out
);
    assign out = 32'd`CONCAT(1,23);
endmodule
module str_macro_mod (
    input  logic        dummy,
    output logic [31:0] out
);
    localparam string myStr = `STR(example_text);
    assign out = 32'd0;
endmodule
module default_arg_macro_mod (
    input  logic [31:0] in,
    output logic [31:0] out
);
    assign out = `MULT(in);
endmodule
module nested_macro_mod (
    input  logic [31:0] in,
    output logic [31:0] out
);
    assign out = `CALL_ADD2(in);
endmodule
module intrinsic_macro_mod (
    input  logic        dummy,
    output logic [31:0] out
);
    localparam string thisFile = `__FILE__;
    localparam int    thisLine = `__LINE__;
    assign out = thisLine;
endmodule
module foo_macro_mod (
    input  logic        dummy,
    output logic [31:0] out
);
    localparam int value_local = `FOO(ONE_LOCAL);
    assign out = value_local;
endmodule
module long_expr_macro_mod (
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] out
);
    `define LONG_EXPR(x,y) x + \
y
    assign out = `LONG_EXPR(a,b);
    `undef LONG_EXPR
endmodule
module escaped_id_macro_mod (
    input  logic        dummy,
    output logic [31:0] out
);
    localparam int `ESC_ID(myvar) = 32'd10;
    assign out = `ESC_ID(myvar);
endmodule
