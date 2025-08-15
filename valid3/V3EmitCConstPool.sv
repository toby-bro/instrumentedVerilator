module scalar_const_xor (
    input  logic [31:0] in_data,
    output logic [31:0] out_data
);
    const logic [31:0] XOR_MASK = 32'hDEAD_BEEF;
    always_comb begin
        out_data = in_data ^ XOR_MASK;
    end
endmodule
module table_lookup (
    input  logic [3:0] addr,
    output logic [7:0] data
);
    const logic [7:0] LUT [0:15] = '{
        8'h00, 8'h11, 8'h22, 8'h33,
        8'h44, 8'h55, 8'h66, 8'h77,
        8'h88, 8'h99, 8'hAA, 8'hBB,
        8'hCC, 8'hDD, 8'hEE, 8'hFF
    };
    always_comb begin
        data = LUT[addr];
    end
endmodule
module hello_string (
    input  logic unused_in,
    output logic [7:0] first_char
);
    const string HELLO_MSG = "Hello, Verilator!";
    always_comb begin
        first_char = HELLO_MSG[0];
    end
endmodule
module wide_const_select (
    input  logic sel,
    output logic [127:0] data_out
);
    const logic [127:0] WIDE_CONST = 128'h0123_4567_89AB_CDEF_FEDC_BA98_7654_3210;
    always_comb begin
        if (sel)
            data_out = WIDE_CONST;
        else
            data_out = 128'h0;
    end
endmodule
module multi_dim_const (
    input  logic [1:0] row,
    input  logic [1:0] col,
    output logic [31:0] value
);
    const int MEM [0:3][0:3] = '{
        '{ 0,  1,  2,  3},
        '{ 4,  5,  6,  7},
        '{ 8,  9, 10, 11},
        '{12, 13, 14, 15}
    };
    always_comb begin
        value = MEM[row][col];
    end
endmodule
module struct_const_pack (
    input  logic dummy_in,
    output logic [11:0] combined_out
);
    typedef struct packed {
        logic [3:0] a;
        logic [7:0] b;
    } my_s_t;
    const my_s_t SVAL = '{a:4'hA, b:8'h5A};
    always_comb begin
        combined_out = {SVAL.a, SVAL.b};
    end
endmodule
module real_const_val (
    input  logic flag,
    output real out_real
);
    const real PI_VAL = 3.1415926535;
    always_comb begin
        if (flag)
            out_real = PI_VAL;
        else
            out_real = 0.0;
    end
endmodule
module enum_const_example (
    input  logic [1:0] idx,
    output logic [1:0] color_out
);
    typedef enum logic [1:0] {RED=2'd0, GREEN=2'd1, BLUE=2'd2, YELLOW=2'd3} color_e;
    const color_e COLORS [0:3] = '{RED, GREEN, BLUE, YELLOW};
    always_comb begin
        color_out = COLORS[idx];
    end
endmodule
