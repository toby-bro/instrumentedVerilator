module enum_conditional_mod (
    input  logic [31:0] sel_i,
    output logic [1:0]  enum_o
);
    typedef enum logic [1:0] { EA = 2'd0, EB = 2'd1 } enum_t;
    enum_t foo;
    always_comb begin
        foo = sel_i ? EA : EB;
    end
    assign enum_o = foo;
endmodule
module struct_assign_mod (
    input  logic [3:0] in_a,
    input  logic [7:0] in_b,
    output logic [7:0] out_b
);
    typedef struct packed { logic [3:0] a; logic [7:0] b; } s_t1;
    typedef struct packed { logic [3:0] a; logic [7:0] b; } s_t2;
    s_t1 s1;
    s_t2 s2;
    always_comb begin
        s1 = '{a: in_a, b: in_b};
        s2 = s1;
    end
    assign out_b = s2.b;
endmodule
module union_member_assign_mod (
    input  logic [7:0] in_byte,
    output logic [3:0] out_nibble
);
    typedef union packed {
        logic [7:0] byte_view;
        logic [7:0] byte_dup;
    } u_t;
    u_t uvar;
    always_comb begin
        uvar = in_byte;
    end
    assign out_nibble = uvar.byte_dup[3:0];
endmodule
module array_dim_conv_mod (
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    logic [1:0][3:0] two_by_four;
    logic [7:0]      linear_vec;
    always_comb begin
        two_by_four = {in_data[7:4], in_data[3:0]};
        linear_vec  = two_by_four;
    end
    assign out_data = linear_vec;
endmodule
module bitstream_cast_mod (
    input  logic [31:0] in_bus,
    output logic [15:0] high_o
);
    typedef struct packed {
        logic [15:0] low;
        logic [15:0] high;
    } word_t;
    word_t w;
    always_comb begin
        w = word_t'(in_bus);
    end
    assign high_o = w.high;
endmodule
module streaming_concat_mod (
    input  logic [7:0] byte0_i,
    input  logic [7:0] byte1_i,
    output logic [15:0] word_o
);
    logic [15:0] tmp;
    always_comb begin
        tmp = {<<{byte1_i, byte0_i}};
    end
    assign word_o = tmp;
endmodule
module sign_width_conv_mod (
    input  logic signed [15:0] in_signed,
    output logic [7:0] out_narrow
);
    assign out_narrow = in_signed;
endmodule
module pattern_cast_mod (
    input  logic [3:0] in4,
    output logic [7:0] out8
);
    typedef logic [7:0] byte_t;
    logic [7:0] vec8;
    always_comb begin
        vec8 = byte_t'({in4, in4});
    end
    assign out8 = vec8;
endmodule
