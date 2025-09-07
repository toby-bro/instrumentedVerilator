module ph_and_self #(parameter W = 8) (
    input  logic [W-1:0] a,
    output logic [W-1:0] y
);
    assign y = (a & a) & ((~a) & a);
endmodule
module ph_or_zero_ones (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] y
);
    assign y = (a | 8'h00) | ((~a) | a) | 8'hFF | b;
endmodule
module ph_xor_patterns (
    input  logic [7:0] a,
    output logic [7:0] y
);
    assign y = (a ^ a) ^ 8'hFF;
endmodule
module ph_concat_sel_low (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [3:0] y
);
    wire [7:0] cat = {a, b};
    assign y = cat[3:0];
endmodule
module ph_concat_sel_straddle (
    input  logic [5:0] a,
    input  logic [5:0] b,
    output logic [5:0] y
);
    wire [11:0] cat = {a, b};
    assign y = cat[8:3];
endmodule
module ph_cond_same (
    input  logic        sel,
    input  logic [7:0]  a,
    output logic [7:0]  y
);
    assign y = sel ? a : a;
endmodule
module ph_cond_else_zero (
    input  logic        sel,
    input  logic [7:0]  a,
    output logic [7:0]  y
);
    assign y = sel ? a : 8'h00;
endmodule
module ph_replicate_once (
    input  logic [7:0] a,
    output logic [7:0] y
);
    assign y = {1{a}};
endmodule
module ph_extend_widen (
    input  logic [7:0] a,
    output logic [15:0] y
);
    assign y = a;
endmodule
module ph_shiftl_select(
    input  logic [7:0] a,
    output logic [7:0] y
);
    logic [15:0] tmp;
    logic [15:0] shifted;
    assign tmp = {a, a};
    assign shifted = tmp << 1;
    assign y = shifted[7:0];
endmodule
module ph_shiftr_zero (
    input  logic [7:0] a,
    output logic [7:0] y
);
    assign y = {8'h00, a} >> 8;
endmodule
module ph_reduction_and (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic       y
);
    assign y = &(a & b);
endmodule
module ph_not_not (
    input  logic [7:0] a,
    output logic [7:0] y
);
    assign y = ~(~a);
endmodule
module ph_not_eq (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic       y
);
    assign y = ~(a == b);
endmodule
module ph_not_neq (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic       y
);
    assign y = ~(a != b);
endmodule
module ph_assoc_comm (
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic [7:0] c,
    output logic [7:0] y
);
    assign y = (a & (b & c)) & 8'hFF;
endmodule
module ph_distribute (
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic [7:0] c,
    output logic [7:0] y
);
    assign y = a & (b | c);
endmodule
module ph_bitwise_concat(
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [3:0] y
);
    logic [7:0] cat_masked;
    assign cat_masked = ({a, b} & 8'h0F);
    assign y = cat_masked[3:0];
endmodule
