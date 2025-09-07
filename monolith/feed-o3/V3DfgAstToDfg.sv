module dfg_arith(
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] y_add,
    output logic [31:0] y_sub,
    output logic [31:0] y_mul,
    output logic [31:0] y_div,
    output logic [31:0] y_mod,
    output logic [31:0] y_neg
);
    assign y_add = a + b;
    assign y_sub = a - b;
    assign y_mul = a * b;
    assign y_div = a / b;
    assign y_mod = a % b;
    assign y_neg = -a;
endmodule
module dfg_logic(
    input  logic [15:0] x,
    input  logic [15:0] y,
    output logic [15:0] out_and,
    output logic [15:0] out_or,
    output logic [15:0] out_xor,
    output logic [15:0] out_shiftl_const,
    output logic [15:0] out_shiftr_const,
    output logic [15:0] out_not
);
    assign out_and           = x & y;
    assign out_or            = x | y;
    assign out_xor           = x ^ y;
    assign out_shiftl_const  = x << 2;
    assign out_shiftr_const  = y >> 2;
    assign out_not           = ~x;
endmodule
module dfg_compare(
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic        eq,
    output logic        neq,
    output logic        lt,
    output logic        lte,
    output logic        gt,
    output logic        gte
);
    assign eq  = (a == b);
    assign neq = (a != b);
    assign lt  = (a <  b);
    assign lte = (a <= b);
    assign gt  = (a >  b);
    assign gte = (a >= b);
endmodule
module dfg_concat_slice(
    input  logic [7:0] in0,
    input  logic [7:0] in1,
    output logic [15:0] concat_out,
    output logic [3:0]  slice_out
);
    logic [7:0] temp;
    assign {temp[7:4], temp[3:0]} = in0;
    assign concat_out = {in1, temp};
    assign slice_out  = in0[3:0];
endmodule
module dfg_array_assign(
    input  logic [15:0] in_bits,
    output logic [15:0] out_bits
);
    logic [7:0] arr_in  [0:1];
    logic [7:0] arr_out [0:1];
    always_comb begin
        {arr_in[1], arr_in[0]} = in_bits;
        arr_out = arr_in;
    end
    assign out_bits = {arr_out[1], arr_out[0]};
endmodule
module dfg_conditional(
    input  logic [7:0] data_a,
    input  logic [7:0] data_b,
    input  logic [7:0] data_c,
    input  logic       sel,
    output logic [7:0] out
);
    always_comb begin
        if (sel) out = data_a;
        else     out = data_b + data_c;
    end
endmodule
module dfg_slice_assignment(
    input  logic [7:0] a,
    input  logic [7:0] b,
    output wire  [7:0] y
);
    assign y[3:0] = a[3:0];
    assign y[7:4] = b[3:0];
endmodule
module dfg_reduction(
    input  logic [7:0] in,
    output logic       any1,
    output logic       all1,
    output logic       parity
);
    assign any1   = |in;  
    assign all1   = &in;  
    assign parity = ^in;  
endmodule
module dfg_replication(
    input  logic [3:0]  in,
    output logic [15:0] out_rep
);
    assign out_rep = {4{in}};
endmodule
module dfg_shift_var(
    input  logic [15:0] data,
    input  logic [3:0]  amt,
    output logic [15:0] out_shl,
    output logic [15:0] out_shr
);
    assign out_shl = data << amt;
    assign out_shr = data >> amt;
endmodule
module dfg_mux(
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic       sel,
    output logic [7:0] y
);
    assign y = sel ? a : b;
endmodule
