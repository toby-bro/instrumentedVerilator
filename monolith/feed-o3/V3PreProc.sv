`ifndef WIDTH
`define WIDTH 8
`endif
`define STRIFY(x) `"x`"
`define MAKE_NAME(a,b) a``_``b
`define CONCAT(a,b) a``b
`define ADD(a,b) ((a)+(b))
`define USE_AND
`define FOO 1
module pass_through #(parameter W = `WIDTH) (
    input  logic [W-1:0] din,
    output logic [W-1:0] dout
);
    assign dout = din;
endmodule
module join_test (
    input  logic [3:0] in,
    output logic [3:0] out
);
    logic [3:0] `MAKE_NAME(my,signal);
    assign `MAKE_NAME(my,signal) = in;
    assign out = `MAKE_NAME(my,signal);
endmodule
module cond_test (
    input  logic a,
    input  logic b,
    output logic y
);
`ifdef USE_AND
    assign y = a & b;
`else
    assign y = a | b;
`endif
endmodule
module expr_ifdef_test (
    input  logic  in_sig,
    output logic  out_sig
);
`ifdef FOO
`ifndef BAR
    assign out_sig = in_sig;
`else
    assign out_sig = ~in_sig;
`endif
`else
    assign out_sig = ~in_sig;
`endif
endmodule
module strify_test (
    input  logic in_sig,
    output logic out_sig
);
    localparam string MSG = `STRIFY(StrifyMsg);
    assign out_sig = in_sig;
endmodule
`define TEMP 1
`undef  TEMP
module undef_test (
    input  logic in_sig,
    output logic out_sig
);
`ifdef TEMP
    assign out_sig = in_sig;
`else
    assign out_sig = ~in_sig;
`endif
endmodule
module case_test (
    input  logic [1:0] sel,
    input  logic       in0,
    input  logic       in1,
    input  logic       in2,
    input  logic       in3,
    output logic       out
);
    always_comb begin
        case (sel)
            2'b00: out = in0;
            2'b01: out = in1;
            2'b10: out = in2;
            default: out = in3;
        endcase
    end
endmodule
module line_test (
    input  logic in_sig,
    output logic out_sig
);
`line 200 "virtual.sv" 0
    assign out_sig = in_sig;
`line 300 "virtual.sv" 0
endmodule
`undefineall
