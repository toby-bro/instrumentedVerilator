`ifndef PREPROC_STRESS_GUARD
`define PREPROC_STRESS_GUARD
`define ADD_MACRO(a, b) ((a) + (b))
`define STRIFY(x) `"x`"
`define WIDTH_MACRO(w = 8) (w)
`define MULTI_LINE(body) \
body
`endif
module adder_using_macro
#(
    parameter STR_ID = `STRIFY(MY_ADDER)
)
(
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [8:0] sum
);
    assign sum = `ADD_MACRO(a, b);
endmodule
module width_param_default
#(
    parameter int WIDTH = `WIDTH_MACRO()
)
(
    input  logic [WIDTH-1:0] data_i,
    output logic [WIDTH-1:0] data_o
);
    always_comb begin
        `MULTI_LINE(
            data_o = data_i;
        )
    end
endmodule
module comment_variations
(
    input  logic in_sig,
    output logic out_sig
);
    assign out_sig = in_sig;
endmodule
`define FEATURE_FLAG
module ifdef_feature
(
    input  logic d_in,
    output logic d_out
);
`ifdef FEATURE_FLAG
    assign d_out = d_in;
`else
    assign d_out = ~d_in;
`endif
endmodule
module protect_pragmas_holder
(
    input  logic sig_i,
    output logic sig_o
);
`ifdef NEVER_PROTECT
`pragma protect begin_protected
`pragma protect encoding  = (enctype = "base64", line_length = 64, bytes = 16)
`pragma protect data_block
VGhpcyBpcyBhIHRlc3QgZGF0YS4=
`pragma protect end_protected
`endif
    assign sig_o = sig_i;
endmodule
module include_undef_demo
(
    input  logic x_i,
    output logic x_o
);
`ifdef NEVER_INCLUDE
`include "non_existing_file.svh"
`endif
`undef TRIPLE_QUOTED
    assign x_o = x_i;
endmodule
