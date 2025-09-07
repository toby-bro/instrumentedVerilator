module m_unpacked_array_split (
    input  logic [1:0] in0,
    input  logic [1:0] in1,
    output logic [1:0] out0,
    output logic [1:0] out1
);
    logic [1:0] unpacked_array_var [0:1] /*verilator split_var*/;
    always_comb begin
        unpacked_array_var[0]      = in0;
        unpacked_array_var[1][0]   = ~in1[0];
        unpacked_array_var[1][1]   =  in1[1];
        out0                       = unpacked_array_var[1];
        out1                       = {unpacked_array_var[0][1], unpacked_array_var[0][0]};
    end
endmodule
module m_packed_vector_split (
    input  logic        in_cond,
    input  logic        input0,
    input  logic [2:0]  input1,
    output logic [3:0]  out_packed
);
    logic [3:0] packed_var /*verilator split_var*/;
    always_comb begin
        if (in_cond) begin
            packed_var = 4'b0;
        end else begin
            packed_var[3]   = input0;
            packed_var[2:0] = input1;
        end
        out_packed = packed_var;
    end
endmodule
module m_unpacked_struct_split (
    input  logic [7:0] in_byte,
    input  logic       in_flag,
    output logic [7:0] out_byte,
    output logic       out_flag
);
    typedef struct {
        logic [7:0] byte;
        logic       flag;
    } unp_s_t;
    unp_s_t mystruct /*verilator split_var*/;
    always_comb begin
        mystruct.byte = in_byte;
        mystruct.flag = in_flag;
        out_byte      = mystruct.byte;
        out_flag      = mystruct.flag;
    end
endmodule
module m_packed_struct_split (
    input  logic        in_a,
    input  logic [2:0]  in_b,
    output logic [3:0]  out_vec
);
    typedef struct packed {
        logic       a;
        logic [2:0] b;
    } pst_t;
    pst_t pack_struct /*verilator split_var*/;
    always_comb begin
        pack_struct.a = in_a;
        pack_struct.b = in_b;
        out_vec       = {pack_struct.a, pack_struct.b};
    end
endmodule
module m_bitfield_operations (
    input  logic [15:0] in_wide,
    output logic        out_bit,
    output logic [3:0]  out_slice
);
    logic [15:0] wide /*verilator split_var*/;
    always_comb begin
        wide       = in_wide;
        wide[12]   = wide[11] ^ wide[10];
        out_bit    = wide[3];
        out_slice  = wide[7:4];
    end
endmodule
