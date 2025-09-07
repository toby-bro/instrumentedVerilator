module m_varref #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in_p,
    output logic [WIDTH-1:0] out_p
);
    assign out_p = in_p;
endmodule
module m_const (
    input  logic        en,
    output logic [7:0]  out_p
);
    assign out_p = en ? 8'd12 : 8'd0;
endmodule
module m_sel (
    input  logic [7:0] in_p,
    input  logic [1:0] idx,
    output logic [3:0] out_p
);
    assign out_p = in_p[idx +: 4];
endmodule
module m_mux (
    input  logic [3:0] a,
    input  logic [3:0] b,
    input  logic       sel,
    output logic [3:0] out_p
);
    assign out_p = sel ? a : b;
endmodule
module m_concat (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [7:0] out_p
);
    assign out_p = {a, b};
endmodule
module m_replicate (
    input  logic [1:0] a,
    output logic [7:0] out_p
);
    assign out_p = {4{a}};
endmodule
module m_arith (
    input  logic signed [7:0] a,
    input  logic signed [7:0] b,
    output logic signed [7:0] sum,
    output logic signed [7:0] diff,
    output logic signed [7:0] prod,
    output logic signed [7:0] quotient,
    output logic signed [7:0] mod
);
    assign sum      = a + b;
    assign diff     = a - b;
    assign prod     = a * b;
    assign quotient = b != 0 ? a / b : '0;
    assign mod      = b != 0 ? a % b : '0;
endmodule
module m_bitwise (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] and_o,
    output logic [7:0] or_o,
    output logic [7:0] xor_o,
    output logic [7:0] not_a
);
    assign and_o = a & b;
    assign or_o  = a | b;
    assign xor_o = a ^ b;
    assign not_a = ~a;
endmodule
module m_reduce (
    input  logic [7:0] a,
    output logic       and_r,
    output logic       or_r,
    output logic       xor_r
);
    assign and_r = &a;
    assign or_r  = |a;
    assign xor_r = ^a;
endmodule
module m_shift (
    input  logic [7:0] a,
    input  logic [2:0] shift_amt,
    output logic [7:0] shl,
    output logic [7:0] shr,
    output logic [7:0] sar
);
    assign shl = a << shift_amt;
    assign shr = a >> shift_amt;
    assign sar = $signed(a) >>> shift_amt;
endmodule
module m_extend (
    input  logic [3:0] a,
    output logic [7:0] sign_ext,
    output logic [7:0] zero_ext
);
    assign sign_ext = {{4{a[3]}}, a};
    assign zero_ext = {{4{1'b0}}, a};
endmodule
module m_compare (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic       eq,
    output logic       neq,
    output logic       lt,
    output logic       lte,
    output logic       gt,
    output logic       gte
);
    assign eq  = (a == b);
    assign neq = (a != b);
    assign lt  = (a <  b);
    assign lte = (a <= b);
    assign gt  = (a >  b);
    assign gte = (a >= b);
endmodule
module m_array (
    input  logic [7:0] in_arr [0:3],
    input  logic [1:0] idx,
    output logic [7:0] out_p
);
    assign out_p = in_arr[idx];
endmodule
module m_nested_mux (
    input  logic [1:0] sel,
    input  logic [3:0] a,
    input  logic [3:0] b,
    input  logic [3:0] c,
    output logic [3:0] out_p
);
    assign out_p = (sel == 2'd0) ? a :
                   (sel == 2'd1) ? b :
                                   c;
endmodule
module m_case (
    input  logic [1:0] sel,
    input  logic [3:0] a,
    input  logic [3:0] b,
    input  logic [3:0] c,
    input  logic [3:0] d,
    output logic [3:0] out_p
);
    always_comb begin
        case (sel)
            2'd0: out_p = a;
            2'd1: out_p = b;
            2'd2: out_p = c;
            default: out_p = d;
        endcase
    end
endmodule
module m_conditional (
    input  logic       cond1,
    input  logic       cond2,
    input  logic [3:0] a,
    input  logic [3:0] b,
    input  logic [3:0] c,
    output logic [3:0] out_p
);
    assign out_p = cond1 ? (cond2 ? a : b) : c;
endmodule
module m_partsel_dynamic (
    input  logic [15:0] in_p,
    input  logic [3:0]  start,
    output logic [7:0]  out_p
);
    assign out_p = in_p[start +: 8];
endmodule
module m_array_multid (
    input  logic [3:0] in_arr [0:1][0:1],
    input  logic [1:0] idx0,
    input  logic [1:0] idx1,
    output logic [3:0] out_p
);
    assign out_p = in_arr[idx0][idx1];
endmodule
module m_gen_loop (
    input  logic [3:0] a,
    output logic [3:0] out_p
);
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin
            assign out_p[i] = a[3-i];
        end
    endgenerate
endmodule
module m_signed_unsigned (
    input  logic signed [7:0] asigned,
    input  logic       [7:0] aunsigned,
    output logic signed [7:0] sum_su,
    output logic [7:0]        sum_uu
);
    assign sum_su = asigned + $signed(aunsigned);
    assign sum_uu = aunsigned + aunsigned;
endmodule
