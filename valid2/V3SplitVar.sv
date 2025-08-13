module unpack_arr_splitter(
    input  logic [1:0] in0,
    input  logic [1:0] in1,
    output logic [1:0] out0
);
    logic [1:0] uarr[0:1] /*verilator split_var*/;
    always_comb begin
        uarr[0] = in0;
        uarr[1] = {~in1[1], in1[0]};
        out0    = {uarr[1][1], uarr[0][0]};
    end
endmodule
module packed_vec_splitter(
    input  logic        in_bit,
    input  logic [2:0]  in_vec,
    input  logic        cond,
    output logic        out_bit,
    output logic [2:0]  out_vec
);
    logic [3:0] packed_var /*verilator split_var*/;
    always_comb begin
        if (cond) begin
            packed_var = 4'd0;
        end else begin
            packed_var[3]   = in_bit;
            packed_var[2:0] = in_vec;
        end
        out_bit = packed_var[3];
        out_vec = packed_var[2:0];
    end
endmodule
module struct_splitter(
    input  logic [3:0] in_a,
    input  logic       in_b,
    output logic [3:0] out_a,
    output logic       out_b
);
    typedef struct packed {
        logic [3:0] a;
        logic       b;
    } st_t;
    st_t s /*verilator split_var*/;
    always_comb begin
        s.a = in_a;
        s.b = in_b;
        out_a = s.a;
        out_b = s.b;
    end
endmodule
module multi_dim_array_splitter(
    input  logic [7:0] d00, d01, d10, d11,
    output logic [7:0] q00, q01, q10, q11
);
    logic [7:0] matrix[0:1][0:1] /*verilator split_var*/;
    always_comb begin
        matrix[0][0] = d00;
        matrix[0][1] = d01;
        matrix[1][0] = d10;
        matrix[1][1] = d11;
        q00 = matrix[0][0];
        q01 = matrix[0][1];
        q10 = matrix[1][0];
        q11 = matrix[1][1];
    end
endmodule
module auto_packed_splitter(
    input  logic [31:0] in_data,
    output logic [7:0]  out0,
    output logic [7:0]  out1,
    output logic [7:0]  out2,
    output logic [7:0]  out3
);
    logic [31:0] big_vector;
    always_comb begin
        big_vector = in_data;
        out0 = big_vector[7 : 0];
        out1 = big_vector[15: 8];
        out2 = big_vector[23:16];
        out3 = big_vector[31:24];
    end
endmodule
module port_splitter(
    input  logic [7:0] in_bus,
    output logic [7:0] port_out /*verilator split_var*/
);
    always_comb begin
        port_out = in_bus;
    end
endmodule
