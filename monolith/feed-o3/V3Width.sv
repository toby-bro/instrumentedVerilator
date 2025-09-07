module basic_logic #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic red_and,
    output logic red_or ,
    output logic red_xor,
    output logic log_and,
    output logic log_or,
    output logic log_not
);
    assign red_and  = &a;
    assign red_or   = |a;
    assign red_xor  = ^a;
    assign log_and  = (a!=0) && (b!=0);
    assign log_or   = (a!=0) || (b!=0);
    assign log_not  = !(a!=0);
endmodule
module concat_rep (
    input  logic [3:0] in_a,
    input  logic [1:0] in_b,
    output logic [7:0] out_concat,
    output logic [7:0] out_rep
);
    assign out_concat = {in_a, in_b, 2'b11};
    assign out_rep    = {4{in_b}};
endmodule
module shift_ops(
    input  logic signed [15:0] a,
    input  logic [3:0]         sh,
    output logic signed [15:0] lsh,
    output logic signed [15:0] rsh,
    output logic signed [15:0] arsh
);
    assign lsh  = a <<  sh;
    assign rsh  = a >>  sh;
    assign arsh = a >>> sh;
endmodule
module compare_ops(
    input  logic signed [7:0] a,
    input  logic        [7:0] b,
    output logic eq_u,
    output logic eq_s,
    output logic gt_s,
    output logic lt_u
);
    assign eq_u = a == b;
    assign eq_s = $signed(a) == $signed(b);
    assign gt_s = $signed(a)  > $signed(b);
    assign lt_u = a < b;
endmodule
module sign_conv(
    input  logic        [7:0] a,
    input  logic signed [7:0] b,
    output logic signed [8:0] sum_mix,
    output logic signed [7:0] as_signed
);
    assign sum_mix   = $signed({1'b0,a}) + b; 
    assign as_signed = $signed(a);
endmodule
module real_ops(
    input  real r1,
    input  real r2,
    output logic r_gt
);
    assign r_gt = r1 > r2;
endmodule
module struct_pattern(
    input  logic [7:0] in_byte,
    output logic [15:0] out_struct_packed
);
    typedef struct packed {
        logic [7:0] hi;
        logic [7:0] lo;
    } pack_t;
    pack_t val;
    always_comb begin
        val = '{hi : in_byte, lo : 8'h00};
        out_struct_packed = val;
    end
endmodule
module array_pattern(
    input  logic [3:0] nibble,
    output logic [31:0] vec
);
    always_comb begin
        vec = '{default:1'b0};
        vec[3:0] = nibble;
    end
endmodule
