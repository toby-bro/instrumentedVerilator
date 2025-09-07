module reductions (
    input  logic [7:0] x,
    output logic       y_and,
    output logic       y_or,
    output logic       y_xor,
    output logic       y_nor,
    output logic       y_xnor
);
    assign y_and  = &x;
    assign y_or   = |x;
    assign y_xor  = ^x;
    assign y_nor  = ~|x;
    assign y_xnor = ~^x;
endmodule
module arithmetic (
    input  logic signed [3:0] a,
    input  logic signed [3:0] b,
    output logic signed [3:0] sum,
    output logic signed [3:0] diff,
    output logic [7:0]       prod,
    output logic [7:0]       divr,
    output logic [7:0]       modr
);
    assign sum  = a + b;
    assign diff = a - b;
    assign prod = a * b;
    assign divr = a / b;
    assign modr = a % b;
endmodule
module shifts (
    input  logic signed [7:0] a,
    input  logic        [2:0] sh,
    output logic signed [7:0] sll,
    output logic signed [7:0] srl,
    output logic signed [7:0] sra
);
    assign sll = a << sh;
    assign srl = a >> sh;
    assign sra = a >>> sh;
endmodule
module compare_ops (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic       eq,
    output logic       neq,
    output logic       gt,
    output logic       lt,
    output logic       ge,
    output logic       le
);
    assign eq  = (a == b);
    assign neq = (a != b);
    assign gt  = (a >  b);
    assign lt  = (a <  b);
    assign ge  = (a >= b);
    assign le  = (a <= b);
endmodule
module cond_select (
    input  logic [3:0] t,
    input  logic [3:0] f,
    input  logic       sel,
    output logic [3:0] out
);
    assign out = sel ? t : f;
endmodule
module concat_replicate (
    input  logic [1:0] a,
    input  logic [1:0] b,
    output logic [3:0] rep,
    output logic [1:0] cat
);
    assign rep = {4{a[0]}};
    assign cat = {2{a}} ^ {2{b}};
endmodule
module nested_concat (
    input  logic [1:0] a,
    input  logic [1:0] b,
    output logic [5:0] out
);
    assign out = {{2{a[1]}},{b,a}};
endmodule
module conditional_nested (
    input  logic       c1,
    input  logic       c2,
    input  logic [3:0] a,
    input  logic [3:0] b,
    input  logic [3:0] d,
    output logic [3:0] o
);
    assign o = c1 ? (c2 ? a : b) : d;
endmodule
module unary_ops (
    input  logic [7:0] x,
    output logic [7:0] neg,
    output logic       notx
);
    assign neg  = -x;
    assign notx = ~x;
endmodule
module boolean_ops (
    input  logic x,
    input  logic y,
    output logic land,
    output logic lor,
    output logic lnot
);
    assign land = x && y;
    assign lor  = x || y;
    assign lnot = !x;
endmodule
module power_op (
    input  logic [3:0] base,
    input  logic [3:0] exp,
    output logic [7:0] pow
);
    assign pow = base ** exp;
endmodule
module real_cast_ops (
    input  real               r,
    input  logic signed [15:0] i16,
    output real               rn,
    output logic [15:0]       iout
);
    assign rn   = i16;
    assign iout = $rtoi(r);
endmodule
module string_ops (
    input  string s,
    input  byte   c,
    output int    len,
    output string s2,
    output string sl,
    output string su
);
    assign len = s.len();
    assign s2  = {s,string'(c)};
    assign sl  = s.tolower();
    assign su  = s.toupper();
endmodule
module struct_union_example (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [3:0] o_and,
    output logic [3:0] o_or
);
    typedef struct packed { logic [3:0] w; logic [3:0] x; } mystruct;
    typedef union packed { logic [3:0] u1; logic [3:0] u2; } myunion;
    mystruct s1;
    myunion  mu;
    assign s1 = '{a,b};
    assign mu = '{.u2(b)};
    assign o_and = s1.w & s1.x;
    assign o_or  = mu.u2 | s1.w;
endmodule
module slicing_example (
    input  logic [7:0] din,
    output logic [3:0] sel_hi,
    output logic [3:0] sel_lo
);
    assign sel_hi = din[7:4];
    assign sel_lo = din[3:0];
endmodule
module replicate_vec (
    input  logic [1:0] d,
    output logic [7:0] dout
);
    assign dout = {4{d}};
endmodule
module case_example (
    input  logic [1:0] sel,
    output logic       onehot
);
    always_comb begin
        case (sel)
            2'd0,2'd1: onehot = 1;
            2'd2:      onehot = 0;
            default:   onehot = 1;
        endcase
    end
endmodule
module generate_for_example #(
    parameter int N = 4
) (
    input  logic [N-1:0] data,
    output logic [N-1:0] shifted
);
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin
            assign shifted[i] = data[(i+1)%N];
        end
    endgenerate
endmodule
