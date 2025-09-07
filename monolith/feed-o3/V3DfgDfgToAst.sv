//------------------------------------------------------------------------------
module m_arith_logic_shift (
    input  logic [15:0] a,
    input  logic [15:0] b,
    input  logic [3:0]  s,
    output logic [15:0] out_add,
    output logic [15:0] out_sub,
    output logic [31:0] out_mul,
    output logic [15:0] out_div,
    output logic [15:0] out_mod,
    output logic [15:0] out_and,
    output logic [15:0] out_or,
    output logic [15:0] out_xor,
    output logic [31:0] out_shl,
    output logic [15:0] out_shr,
    output logic [15:0] out_shra
);
    assign out_add  = a + b;
    assign out_sub  = a - b;
    assign out_mul  = a * b;
    assign out_div  = a / (b | 16'h0001);      
    assign out_mod  = a % (b | 16'h0001);
    assign out_and  = a & b;
    assign out_or   = a | b;
    assign out_xor  = a ^ b;
    assign out_shl  = {16'd0, a} << s;
    assign out_shr  = a >> s;
    assign out_shra = $signed(a) >>> s;
endmodule
//------------------------------------------------------------------------------
module m_concat_replicate (
    input  logic [7:0] x,
    input  logic [7:0] y,
    output logic [15:0] out_concat,
    output logic [31:0] out_rep
);
    assign out_concat = {x, y};
    assign out_rep    = {4{y}};
endmodule
//------------------------------------------------------------------------------
module m_reduction_conditional (
    input  logic [7:0] data,
    input  logic       sel,
    output logic       redor,
    output logic       redand,
    output logic       redxor,
    output logic [7:0] cond_out
);
    assign redor    = |data;
    assign redand   = &data;
    assign redxor   = ^data;
    assign cond_out = sel ? data : ~data;
endmodule
//------------------------------------------------------------------------------
module m_extend_cast (
    input  logic [7:0] in_small,
    output logic [15:0] zero_ext,
    output logic [15:0] sign_ext
);
    assign zero_ext = in_small;          
    assign sign_ext = $signed(in_small); 
endmodule
//------------------------------------------------------------------------------
module m_dynamic_part_select (
    input  logic [31:0] vector,
    input  logic  [4:0] idx,
    output logic  [7:0] slice
);
    assign slice = vector[idx +: 8];
endmodule
//------------------------------------------------------------------------------
module m_packed_splice (
    input  logic [7:0] lower,
    input  logic [7:0] upper,
    output logic [15:0] packed_out
);
    logic [15:0] temp;
    always_comb begin
        temp        = 16'h0000;
        temp[7:0]   = lower;
        temp[15:8]  = upper;
    end
    assign packed_out = temp;
endmodule
//------------------------------------------------------------------------------
module m_array_splice (
    input  logic [7:0] base,
    input  logic [7:0] extra,
    output logic [15:0] sum_array
);
    logic [7:0] arr[0:3];
    integer i;
    always_comb begin
        for (i = 0; i < 4; i++) begin
            arr[i] = base + i[7:0];
        end
        arr[2] = extra;
    end
    assign sum_array = arr[0] + arr[1] + arr[2] + arr[3];
endmodule
//------------------------------------------------------------------------------
module m_negate_not (
    input  logic [15:0] in_val,
    output logic [15:0] out_neg,
    output logic [15:0] out_not
);
    assign out_neg = -in_val;
    assign out_not = ~in_val;
endmodule
//------------------------------------------------------------------------------
module m_compare (
    input  logic [15:0] a,
    input  logic [15:0] b,
    output logic lt,
    output logic lte,
    output logic gt,
    output logic gte,
    output logic eq,
    output logic neq
);
    assign lt  = a <  b;
    assign lte = a <= b;
    assign gt  = a >  b;
    assign gte = a >= b;
    assign eq  = a == b;
    assign neq = a != b;
endmodule
