module cmp_ops #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic             eq,
    output logic             neq,
    output logic             gt,
    output logic             ge,
    output logic             lt,
    output logic             le
);
    always_comb begin
        eq  = (a == b);
        neq = (a != b);
        gt  = ($signed(a)   >  $signed(b));
        ge  = ($signed(a)   >= $signed(b));
        lt  = ($unsigned(a) <  $unsigned(b));
        le  = ($unsigned(a) <= $unsigned(b));
    end
endmodule
module reduce_ops (
    input  logic [15:0] in_vec,
    output logic        red_or,
    output logic        red_and,
    output logic        red_xor,
    output logic        onehot,
    output logic        onehot0,
    output logic        is_unk
);
    always_comb begin
        red_or  = |in_vec;
        red_and = &in_vec;
        red_xor = ^in_vec;
        onehot  = $onehot (in_vec);
        onehot0 = $onehot0(in_vec);
        is_unk  = $isunknown(in_vec);
    end
endmodule
module concat_rep (
    input  logic [3:0] a,
    input  logic [1:0] b,
    output logic [9:0] c
);
    logic [5:0] rep;
    always_comb begin
        rep = {3{b}};
        c   = {a, rep};
    end
endmodule
module stream_concat (
    input  logic [7:0]  byte_in,
    output logic [31:0] stream_out
);
    always_comb begin
        stream_out = {byte_in, byte_in, byte_in, byte_in};
    end
endmodule
module shift_ops (
    input  logic [31:0] data,
    input  logic [4:0]  shamt,
    output logic [31:0] shl,
    output logic [31:0] shr,
    output logic [31:0] sar
);
    always_comb begin
        shl = data          <<  shamt;
        shr = data          >>  shamt;
        sar = $signed(data) >>> shamt;
    end
endmodule
module cast_ops (
    input  logic [31:0] int_in,
    output real         real_out,
    output logic signed [31:0] signed_out
);
    always_comb begin
        real_out   = $itor(int_in);
        signed_out = $signed(int_in);
    end
endmodule
module sel_ops (
    input  logic [15:0] in_bus,
    output logic [7:0]  upper,
    output logic [7:0]  lower
);
    assign upper = in_bus[15:8];
    assign lower = in_bus[7:0];
endmodule
module attr_ops (
    input  logic        dummy_in,
    output logic [31:0] bits_val,
    output logic [31:0] size_val
);
    logic [3:0][7:0] fixed_array;
    assign bits_val = $bits(fixed_array);
    assign size_val = $size(fixed_array);
endmodule
module signed_extend (
    input  logic signed [7:0] in_val,
    output logic signed [15:0] out_val
);
    assign out_val = $signed(in_val);
endmodule
module unsigned_cast (
    input  logic signed [7:0] in_val,
    output logic [7:0]        out_val
);
    assign out_val = $unsigned(in_val);
endmodule
module const_autoextend (
    input  logic dummy,
    output logic [7:0] full_one
);
    assign full_one = '1;
endmodule
module pattern_struct (
    input  logic dummy,
    output logic [7:0] packed_out
);
    typedef struct packed {
        logic [3:0] lo;
        logic [3:0] hi;
    } my_t;
    my_t st = '{lo:4'hA, hi:4'h5};
    assign packed_out = st;
endmodule
module width_mismatch (
    input  logic [3:0] a,
    output logic [7:0] y
);
    assign y = a + 8'd1;
endmodule
module edge_detect (
    input  logic clk,
    input  logic rst_n,
    input  logic signal_in,
    output logic rose_out,
    output logic fell_out
);
    logic signal_d;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            signal_d <= 1'b0;
        else
            signal_d <= signal_in;
    end
    assign rose_out =  signal_in & ~signal_d;
    assign fell_out = ~signal_in &  signal_d;
endmodule
module real_conv (
    input  logic [63:0] bits_in,
    output real         real_val
);
    always_comb begin
        real_val = $bitstoreal(bits_in);
    end
endmodule
module queue_size (
    input  logic        dummy,
    output logic [31:0] q_size
);
    logic [7:0] q[$];
    always_comb begin
        q_size = q.size();
    end
endmodule
module enum_ops (
    input  logic        dummy,
    input  logic [1:0]  sel,
    output logic [31:0] is_green,
    output logic [1:0]  next_color
);
    typedef enum logic [1:0] { RED   = 2'd0,
                               GREEN = 2'd1,
                               BLUE  = 2'd2 } color_t;
    color_t c_in;
    always_comb begin
        c_in        = color_t'(sel);
        is_green    = (c_in == GREEN);
        next_color  = (c_in == BLUE) ? RED : color_t'(c_in + 1);
    end
endmodule
