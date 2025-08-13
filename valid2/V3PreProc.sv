`define ADD(a,b) ((a)+(b))
`define INCREMENT(x=4) ((x)+1)
`define STRIFY(x) `"x`"
`define GEN_WIRE(name)  wire name``_wire;
`define PREFIX pre
`define SUFFIX suf
`define MAKE_JOIN `PREFIX``_``SUFFIX
`define FEATURE_A
`define FLAG1
module macro_add(
    input  wire [7:0] in1,
    input  wire [7:0] in2,
    output wire [7:0] out
);
    assign out = `ADD(in1, in2);
endmodule
module incr_default(
    input  wire [7:0] in,
    output wire [7:0] out
);
    localparam int PARAM_INC = `INCREMENT();
    assign out = in + PARAM_INC;
endmodule
module stringify_test(
    input  wire  clk,
    output string str_out
);
    localparam string LOCAL_STR = `STRIFY(Verilator_PreProc);
    always_comb begin
        str_out = LOCAL_STR;
    end
endmodule
module token_paste_demo(
    input  wire in_sig,
    output wire out_sig
);
    `GEN_WIRE(my)
    wire `MAKE_JOIN;
    assign my_wire = in_sig;
    assign `MAKE_JOIN = my_wire;
    assign out_sig = `MAKE_JOIN;
endmodule
module conditional_compile(
    input  wire in_bit,
    output wire out_bit
);
`ifdef FLAG1
    assign out_bit = in_bit;
`elsif FEATURE_A
    assign out_bit = ~in_bit;
`else
    assign out_bit = 1'b0;
`endif
endmodule
`define TEMP_MACRO(val) (val)
module undef_test(
    input  wire [3:0] in_data,
    output wire [3:0] out_data
);
    assign out_data = `TEMP_MACRO(in_data);
endmodule
`undef TEMP_MACRO
module undefineall_demo(
    input  wire d_in,
    output wire d_out
);
    assign d_out = d_in;
endmodule
`undefineall
