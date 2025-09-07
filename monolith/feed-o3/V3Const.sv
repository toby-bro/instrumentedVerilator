module bitop_tree(
    input  logic [2:0] v,
    output logic       y
);
    assign y = (3'b011 == (3'b011 & v)) & v[2];
endmodule
module redxor_mask(
    input  logic [15:0] a,
    output logic        y
);
    assign y = ^(16'h00FF & a);
endmodule
module shift_mask(
    input  logic [31:0] b,
    output logic [7:0]  y
);
    assign y = 8'hFF & (b >> 24);
endmodule
module huge_shift(
    input  logic [31:0] a,
    output logic [31:0] y
);
    assign y = a << 64;
endmodule
module replicate_concat(
    input  logic [1:0] d,
    output logic [7:0] y
);
    assign y = {2{{d,d}}};
endmodule
module logical_vs_bitwise(
    input  logic in1,
    input  logic in2,
    output logic out_and,
    output logic out_or
);
    assign out_and = (in1 && in2);
    assign out_or  = (in1 || in2);
endmodule
module select_rep(
    input  logic bit_in,
    output logic y
);
    assign y = {3{bit_in}}[1];
endmodule
module nested_select(
    input  logic [7:0] a,
    output logic       y
);
    logic [15:0] tmp;
    assign tmp = {a, a};
    assign y   = &tmp[15:8];
endmodule
module shift_shift(
    input  logic [31:0] in,
    output logic [31:0] out
);
    assign out = (in << 4) << 5;
endmodule
module double_not(
    input  logic i,
    output logic o
);
    assign o = !( !i );
endmodule
module compare_consts(
    input  logic [31:0] a,
    output logic        eq0,
    output logic        neq1,
    output logic        gt0
);
    assign eq0  = (a == 32'd0);
    assign neq1 = (a != 32'd1);
    assign gt0  = (a  > 32'd0);
endmodule
module and_zero(
    input  logic [7:0] a,
    output logic [7:0] y
);
    assign y = a & 8'h00;
endmodule
module or_ones(
    input  logic [7:0] a,
    output logic [7:0] y
);
    assign y = a | 8'hFF;
endmodule
module redand_concat(
    input  logic [15:0] a,
    output logic        y
);
    assign y = &{a,8'h00};
endmodule
module xor_self(
    input  logic [7:0] a,
    output logic [7:0] y
);
    assign y = a ^ a;
endmodule
