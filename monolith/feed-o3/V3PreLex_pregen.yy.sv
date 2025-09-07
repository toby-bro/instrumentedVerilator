`define AND_WITH_PARAM(a,b) ((a) & (b))
`define STRINGIFY(x) `"x`"
`define ADD_DEFAULT(a, b = 8) ((a) + (b))
`define LONG_MACRO(a,b) ((a) | (b))
`define UNUSED_MACRO "\"Unused\""
`define CONDITION
`undef CONDITION
`pragma foo bar
`pragma protect begin_protected
`pragma protect encoding = (enctype = "BASE64", line_length = 4, bytes = 4)
`pragma protect data_block
QUJD
`pragma protect end_protected
module and_gate(input  logic a, input  logic b, output logic y);
    assign y = `AND_WITH_PARAM(a, b);
endmodule
module example_add_default(input logic [7:0] a, output logic [7:0] y);
    assign y = `ADD_DEFAULT(a);
endmodule
module macro_arith#(parameter int WIDTH = 8)(input logic [WIDTH-1:0] in1, input logic [WIDTH-1:0] in2, output logic [WIDTH-1:0] out_sum);
`ifdef CONDITION
    assign out_sum = in1 - in2;
`elsif OTHERCOND
    assign out_sum = in1 | in2;
`else
    assign out_sum = in1 + in2;
`endif
endmodule
module string_param(input logic dummy_in, output logic dummy_out);
    parameter string TEXT = `STRINGIFY(SampleText);
    assign dummy_out = dummy_in;
endmodule
module comment_demo(input logic clk, output logic q);
    logic r;
    always_ff @(posedge clk) r <= 1'b1;
    assign q = r;
endmodule
