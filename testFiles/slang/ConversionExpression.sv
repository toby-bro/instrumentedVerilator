module m_enum_conditional (
    input  logic [31:0] in_i,
    output logic        out_enum
);
    typedef enum logic { A = 1'b0, B = 1'b1 } e_t;
    e_t foo;
    always_comb begin
        foo      = in_i ? A : B;   
        out_enum = foo;            
    end
endmodule
module m_struct_union (
    input  logic [3:0] in_a,
    input  logic [7:0] in_b,
    output logic [11:0] out_c
);
    typedef struct packed {
        logic [3:0] a;
        logic [7:0] b;
    } packed_s_t;
    packed_s_t s_left, s_right;
    always_comb begin
        s_left.a = in_a;
        s_left.b = in_b;
        s_right  = s_left;
        out_c    = {s_right.a, s_right.b};
    end
endmodule
module m_union_member (
    input  logic [7:0]  in_byte,
    output logic [31:0] out_word
);
    typedef union packed {
        logic [31:0]           w;
        logic [3:0][7:0]       bytes;   
    } u_packed_t;
    u_packed_t u;
    always_comb begin
        u.w          = 32'h0;
        u.bytes[0]   = in_byte;   
        out_word     = u.w;       
    end
endmodule
module m_multidim_array (
    input  logic [7:0]       in_flat,
    output logic [1:0][3:0]  out_arr
);
    logic [1:0][3:0] arr_md;
    logic [7:0]      flat_var;
    always_comb begin
        flat_var = in_flat;  
        arr_md   = flat_var; 
        out_arr  = arr_md;
    end
endmodule
module m_casts (
    input  logic  [7:0] in_data,
    output logic signed [7:0] out_signed,
    output logic        [7:0] out_unsigned,
    output logic        [3:0] out_small
);
    always_comb begin
        out_signed   = signed'(in_data);
        out_unsigned = unsigned'(out_signed);
        out_small    = 4'(in_data);
    end
endmodule
