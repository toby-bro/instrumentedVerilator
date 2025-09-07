`line 1000 "generated.sv" 0
`define ADD(a,b)       ((a)+(b))
`define DOUBLE(x)      ((x)<<1)
`define STR(s)         `"s`"
`define CONCAT(a,b)    a``b
`define PREFIX(x)      pre_``x
`define BOOL_FLAG      1
`define REF_MACRO      `BOOL_FLAG
`define DEFARG_SAMPLE(x=8) ((x)*2)
`define COMPOSED(y)    `DOUBLE(y)
/* multiline define, uses back-slash newline */
`define MULTILINE_VAL \
1 + \
1
`define TEMP_FOR_UNDEF 123
module arithmetic_macros (
    input  logic [7:0] a,
    output logic [7:0] y
);
    assign y = `ADD(a, 8'h01);
endmodule
module concat_macro (
    input  logic in,
    output logic out
);
    logic `PREFIX(sig);          
    assign `PREFIX(sig) = in;    
    assign out          = `PREFIX(sig);
endmodule
module stringify_macro (
    input  logic  in,
    output logic  out
);
    localparam string MSG = `STR(HELLO_WORLD); 
    logic unused;
    assign unused = MSG.len() > 0;
    assign out    = in;
endmodule
module ifdef_expr (
    input  logic i,
    output logic o
);
`ifdef (`BOOL_FLAG && 1)
    assign o = i;
`else
    assign o = ~i;
`endif
endmodule
module case_comment (
    input  logic [1:0] sel,
    input  logic       in0,
    input  logic       in1,
    input  logic       in2,
    input  logic       in3,
    output logic       out
);
    always_comb begin
        /* synopsys full_case parallel_case */
        /*verilator public_flat_rw*/
        case (sel)
            2'd0: out = in0;
            2'd1: out = in1;
            2'd2: out = in2;
            default: out = in3;
        endcase
    end
endmodule
module undefineall_mod (
    input  logic a,
    output logic y
);
    `define LOCAL_TMP a
    `undef  LOCAL_TMP
    `undefineall          
    assign y = a;         
endmodule
