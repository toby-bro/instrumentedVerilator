module red_ops(
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic       red_and,
    output logic       red_or,
    output logic       red_xor
);
    logic [7:0] tmp_and = (a & b) & 8'hFF;
    logic [7:0] tmp_or  = (a | b) | 8'h00;
    logic [7:0] tmp_xor = (a ^ b) ^ 8'h00;
    assign red_and = &tmp_and;
    assign red_or  = |tmp_or;
    assign red_xor = ^tmp_xor;
endmodule
module logical_to_bit(
    input  logic a,
    input  logic b,
    output logic y
);
    assign y = (a && b) || (!a && !b);
endmodule
module double_not(
    input  logic [7:0] d,
    output logic [7:0] y
);
    assign y = ~(~d);
endmodule
module concat_select(
    input  logic [7:0] upper,
    input  logic [7:0] lower,
    output logic [15:0] combined,
    output logic [7:0]  slice_hi,
    output logic [7:0]  slice_lo
);
    assign combined = {upper, lower};
    assign slice_hi = combined[15:8];
    assign slice_lo = combined[7:0];
endmodule
module replicate_demo(
    input  logic       in_bit,
    input  logic [1:0] pair_bits,
    output logic [7:0] rep_pair,
    output logic [5:0] nested_rep
);
    assign rep_pair   = {4{pair_bits}};
    assign nested_rep = {3{{2{in_bit}}}};
endmodule
module cond_const(
    input  logic       sel,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    assign dout = sel ? din : 8'h00;
endmodule
module compare_zero_one(
    input  logic [7:0] data,
    output logic       is_zero,
    output logic       is_nonzero,
    output logic       is_allones
);
    assign is_zero    = (data == 8'h00);
    assign is_nonzero = (data != 8'h00);
    assign is_allones = (data == 8'hFF);
endmodule
module compare_ops(
    input  logic [7:0] x,
    input  logic [7:0] y,
    output logic gt,
    output logic gte,
    output logic lt,
    output logic lte
);
    assign gt  = x >  y;
    assign gte = x >= y;
    assign lt  = x <  y;
    assign lte = x <= y;
endmodule
module shift_ops(
    input  logic [63:0] data,
    input  logic [5:0]  shamt,
    output logic [63:0] lshift,
    output logic [63:0] rshift,
    output logic [63:0] arshift
);
    assign lshift  = data << shamt;
    assign rshift  = data >> shamt;
    assign arshift = $signed(data) >>> shamt;
endmodule
module pow_two(
    input  logic [3:0] exp,
    output logic [15:0] result
);
    assign result = 16'h1 << exp;
endmodule
module shift_shift(
    input  logic [15:0] d,
    output logic [15:0] y
);
    assign y = (d << 4) >> 2;
endmodule
module select_examples(
    input  logic [129:0] wide,
    output logic         mid_bit,
    output logic [7:0]   byte_sel
);
    assign mid_bit  = wide[65];
    assign byte_sel = wide[15:8];
endmodule
module bit_tree_example(
    input  logic [3:0] v,
    output logic       tree_and,
    output logic       tree_or,
    output logic       tree_xor
);
    assign tree_and = &(1'b1 & v);
    assign tree_or  = |((2'b11 & v) != 2'b00);
    assign tree_xor = ^((~v) ^ v);
endmodule
module extend_cast(
    input  logic signed [7:0] s_in,
    input  logic        [7:0] u_in,
    output logic signed [15:0] sext,
    output logic        [15:0] uext
);
    assign sext = $signed(s_in);
    assign uext = $unsigned(u_in);
endmodule
module complex_condition(
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic       flag
);
    assign flag = ((a & b) == 8'h00) ? 1'b0 :
                  ((a | b) == 8'hFF) ? 1'b1 :
                  &(a ^ b);
endmodule
