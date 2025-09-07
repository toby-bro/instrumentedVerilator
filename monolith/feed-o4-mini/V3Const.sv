module count_trailing_zero #(parameter WIDTH = 64) (
    input  wire [WIDTH-1:0]        in,
    output reg  [$clog2(WIDTH):0]  count
);
    integer i;
    always_comb begin
        count = $clog2(WIDTH);
        for (i = 0; i < WIDTH; i = i + 1) begin
            if (in[i]) begin
                count = i;
                break;
            end
        end
    end
endmodule
module is_pow2 #(parameter WIDTH = 64) (
    input  wire [WIDTH-1:0] in,
    output wire             is_pow2
);
    assign is_pow2 = (in != 0) && ((in & (in - 1)) == 0);
endmodule
module mask_and_shift #(parameter WIDTH = 32) (
    input  wire [WIDTH-1:0]         data,
    input  wire [WIDTH-1:0]         mask,
    input  wire [$clog2(WIDTH)-1:0] shift_amt,
    output wire [WIDTH-1:0]         out
);
    wire [WIDTH-1:0] masked = data & mask;
    wire mask_all_ones = (mask == {WIDTH{1'b1}});
    assign out = (mask_all_ones ? data : masked) >> shift_amt;
endmodule
module reduction_ops #(parameter N = 8) (
    input  wire [N-1:0] in,
    output wire         red_and,
    output wire         red_or,
    output wire         red_xor
);
    assign red_and = &in;
    assign red_or  = |in;
    assign red_xor = ^in;
endmodule
module word_selector #(parameter WIDTH = 32) (
    input  wire [WIDTH-1:0]         data,
    input  wire [$clog2(WIDTH)-1:0] idx,
    output wire                     bit_out
);
    assign bit_out = data[idx];
endmodule
module adder_subtractor #(parameter WIDTH = 16) (
    input  wire signed [WIDTH-1:0] a,
    input  wire signed [WIDTH-1:0] b,
    input  wire signed [WIDTH-1:0] c,
    output wire signed [WIDTH-1:0] sum,
    output wire signed [WIDTH-1:0] diff
);
    assign sum  = a + b;
    assign diff = a + b - c;
endmodule
module reorder_sub_add #(parameter WIDTH = 16) (
    input  wire signed [WIDTH-1:0] a,
    input  wire signed [WIDTH-1:0] x,
    input  wire signed [WIDTH-1:0] y,
    output wire signed [WIDTH-1:0] out
);
    assign out = a + (x - y);
endmodule
module conditional_operator #(parameter WIDTH = 8) (
    input  wire               cond,
    input  wire [WIDTH-1:0]   thenp,
    input  wire [WIDTH-1:0]   elsep,
    output wire [WIDTH-1:0]   out
);
    assign out = cond ? thenp : elsep;
endmodule
module or_and_simplify #(parameter WIDTH = 8) (
    input  wire [WIDTH-1:0] val,
    input  wire [WIDTH-1:0] a,
    input  wire [WIDTH-1:0] b,
    output wire [WIDTH-1:0] out1,
    output wire [WIDTH-1:0] out2
);
    assign out1 = (val & a) | (val & b);
    assign out2 = val & (a | b);
endmodule
module masked_or_simplify #(parameter WIDTH = 8) (
    input  wire [WIDTH-1:0] mask,
    input  wire [WIDTH-1:0] a,
    input  wire [WIDTH-1:0] b,
    output wire [WIDTH-1:0] out
);
    assign out = mask & (a | b);
endmodule
module or_and_not_simplify #(parameter WIDTH = 8) (
    input  wire [WIDTH-1:0] a,
    input  wire [WIDTH-1:0] b,
    input  wire [WIDTH-1:0] c,
    output wire [WIDTH-1:0] out
);
    assign out = a | (~b & c);
endmodule
module replicate_concat #(parameter WIDTH = 8, parameter REP = 3) (
    input  wire [WIDTH-1:0]      in,
    output wire [REP*WIDTH-1:0]  out
);
    assign out = {REP{in}};
endmodule
module nested_concat_swap #(parameter A=2, B=3, C=4) (
    input  wire [A-1:0] a,
    input  wire [B-1:0] b,
    input  wire [C-1:0] c,
    output wire [A+B+C-1:0] out1,
    output wire [A+B+C-1:0] out2,
    output wire [A+B+C-1:0] out3
);
    assign out1 = {a, b, c};
    assign out2 = {a, {b, c}};
    assign out3 = {{a, b}, c};
endmodule
module sel_extend #(parameter W = 16, parameter NEWW = 8) (
    input  wire [W-1:0] in,
    output wire [NEWW-1:0] out
);
    assign out = in[NEWW-1:0];
endmodule
module sel_bi_lower #(parameter W = 16, parameter L = 8) (
    input  wire [W-1:0] a,
    input  wire [W-1:0] b,
    output wire [L-1:0] out
);
    wire [W:0] sum = a + b;
    assign out = sum[L-1:0];
endmodule
module sel_shift_lower #(parameter W = 16, parameter OW = 8) (
    input  wire [W-1:0]           a,
    input  wire [$clog2(W)-1:0]   shift,
    output wire [OW-1:0]          out
);
    wire [W-1:0] sh = a >> shift;
    assign out = sh[OW-1:0];
endmodule
module double_replicate #(parameter WIDTH = 4) (
    input  wire [WIDTH-1:0] in,
    output wire [2*WIDTH-1:0] out
);
    wire [WIDTH*2-1:0] r1 = {2{in}};
    wire [WIDTH*4-1:0] r2 = {2{r1}};
    assign out = r2;
endmodule
module not_not_simplify (
    input  wire x,
    output wire y
);
    assign y = ~(~x);
endmodule
module equality_reduction_simplify #(parameter WIDTH = 8) (
    input  wire [WIDTH-1:0] a,
    input  wire [WIDTH-1:0] b,
    output wire            eq,
    output wire            neq
);
    assign eq  = (a == b);
    assign neq = (a != b);
endmodule
module bitwise_to_logical #(parameter WIDTH = 1) (
    input  wire [WIDTH-1:0] a,
    input  wire [WIDTH-1:0] b,
    output wire            and2,
    output wire            or2
);
    wire [WIDTH-1:0] band = a & b;
    wire [WIDTH-1:0] bor  = a | b;
    assign and2 = |band;
    assign or2  = |bor;
endmodule
