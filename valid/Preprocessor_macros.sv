`define BASE_WIDTH 8
`define ONE 1
`define TWO 2
`define ADD(a, b) ((a) + (b))
`define SCALE(value, factor = 4) ((value) * (factor))
`define MAKE_STRING(arg) `"arg`"
`define MAKE_WIRE(name)  wire name``_tmp;
`define MULTI_LINE(a, b) (a + \
                           b)
`define IDENTITY(bar) `bar
`define CONCAT3(a, b, c) a``b``c
`define VAL 42
module basic_mod #(parameter int W = `BASE_WIDTH)
                  (input  logic [W-1:0] in,
                   output logic [W-1:0] out);
    assign out = in;
endmodule
module add_mod (input  logic [7:0] in_a,
                input  logic [7:0] in_b,
                output logic [8:0] out_sum);
    assign out_sum = `ADD(in_a, in_b);
endmodule
module scale_mod (input  logic [7:0]  in_val,
                  output logic [15:0] out_val);
    assign out_val = `SCALE(in_val);
endmodule
module string_mod (input  logic  dummy,
                   output logic  flag);
    localparam string S = `MAKE_STRING(hello_world);
    assign flag = (S != "");
endmodule
module paste_mod (input  logic dummy,
                  output logic result);
    `MAKE_WIRE(signal)
    assign signal_tmp = dummy;
    assign result     = signal_tmp;
endmodule
module multi_line_mod (input  logic [7:0] a,
                       input  logic [7:0] b,
                       output logic [8:0] sum);
    assign sum = `MULTI_LINE(a, b);
endmodule
module identity_mod (input  logic        dummy,
                     output logic [15:0] value_out);
    localparam int V = `IDENTITY(VAL);
    assign value_out = V;
endmodule
module builtin_mod (input  logic        dummy,
                    output logic [31:0] line_out);
    localparam string FILE_NAME = `__FILE__;
    localparam int    LINE_NO   = `__LINE__;
    assign line_out = LINE_NO;
endmodule
