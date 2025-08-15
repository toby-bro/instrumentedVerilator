module add_zero_right(
    input  logic [7:0] a,
    output logic [7:0] y
);
    assign y = a + 8'd0;
endmodule
module add_zero_left(
    input  logic [7:0] a,
    output logic [7:0] y
);
    assign y = 8'd0 + a;
endmodule
module and_or_patterns(
    input  logic [7:0] a,
    output logic [7:0] y_and0,
    output logic [7:0] y_and_allones,
    output logic [7:0] y_or0,
    output logic [7:0] y_or_allones
);
    assign y_and0        = a & 8'd0;
    assign y_and_allones = a & 8'hFF;
    assign y_or0         = a | 8'd0;
    assign y_or_allones  = a | 8'hFF;
endmodule
module xor_patterns(
    input  logic [7:0] a,
    output logic [7:0] y_xor0,
    output logic [7:0] y_xor_allones
);
    assign y_xor0        = a ^ 8'd0;
    assign y_xor_allones = a ^ 8'hFF;
endmodule
module shift_patterns(
    input  logic [7:0] a,
    output logic [7:0] shl_zero_amt,
    output logic [7:0] shr_zero_amt,
    output logic [7:0] shl_large_amt
);
    assign shl_zero_amt  = a << 5'd0;
    assign shr_zero_amt  = a >> 5'd0;
    assign shl_large_amt = a << 6'd20;
endmodule
module comparison_patterns(
    input  logic [7:0] a,
    output logic eq_same,
    output logic neq_same,
    output logic lt_same,
    output logic lte_zero,
    output logic gt_zero,
    output logic gte_allones
);
    assign eq_same      = (a == a);
    assign neq_same     = (a != a);
    assign lt_same      = (a <  a);
    assign lte_zero     = (8'd0 <= a);
    assign gt_zero      = (a >  8'd0);
    assign gte_allones  = (a >= 8'hFF);
endmodule
module ternary_patterns(
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] y_zero_cond,
    output logic [7:0] y_one_cond
);
    assign y_zero_cond = (1'b0 ? a : b);
    assign y_one_cond  = (1'b1 ? a : b);
endmodule
module replicate_concat_patterns(
    input  logic [3:0] a,
    output logic [3:0] rep_one,
    output logic       red_and_full,
    output logic [7:0] concat_adj
);
    assign rep_one       = {1{a}};
    assign red_and_full  = &{a,4'hF};
    assign concat_adj    = {a[1],a[0],6'd0};
endmodule
