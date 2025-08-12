interface simple_if;
    logic clk;
    modport mp (input clk);
endinterface
typedef struct packed { logic [3:0] data; } forward_struct_t;
typedef union tagged {
    int  i;
    real r;
} tagged_u_t;
typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
} nibbles_t;
typedef union packed {
    logic [7:0] as_byte;
    nibbles_t   nib;
} packed_u_t;
typedef struct {
    int  x;
    real y;
} unpacked_s_t;
module predefined_ints (
    input  byte      in_byte,
    input  shortint  in_short,
    input  longint   in_long,
    output int       out_sum
);
    time     t0;
    integer  i0;
    assign out_sum = in_byte + in_short + in_long + i0 + t0;
endmodule
module scalar_float (
    input  bit        in_bit,
    input  logic      in_logic,
    input  shortreal  in_sr,
    input  real       in_real,
    output logic      out_logic
);
    real real_sum;
    always_comb begin
        real_sum = in_sr + in_real;
    end
    assign out_logic = in_bit & in_logic;
endmodule
module enum_var (
    input  logic dummy_in,
    output logic dummy_out
);
    typedef enum int { STATE0 = 0, STATE1[3:1] } enum_t;
    enum_t e_var;
    assign dummy_out = dummy_in;
endmodule
module packed_array_demo (
    input  logic [7:0] in_data,
    output logic       out_bit
);
    bit [3:0][7:0] vec;
    always_comb begin
        vec[0] = in_data;
    end
    assign out_bit = vec[0][0];
endmodule
module struct_union_demo (
    input  logic [7:0] in_byte,
    output logic [7:0] out_byte
);
    packed_u_t u;
    always_comb begin
        u.as_byte = in_byte;
        out_byte  = {u.nib.hi, u.nib.lo};
    end
endmodule
module advanced_arrays (
    input  logic        clk,
    input  logic        rst_n,
    output logic [31:0] size_sum
);
    int dyn_array[];
    int queue_array[$:4];
    int assoc_array[string];
    assign size_sum = 32'd0;
endmodule
module virtual_if_demo (
    input  logic clk,
    output logic out_clk
);
    virtual simple_if.mp vif;
    assign out_clk = clk;
endmodule
module typedef_demo (
    input  logic [3:0] in_val,
    output logic [3:0] out_val
);
    typedef int my_int_t;
    typedef struct { my_int_t val; } my_struct_t;
    my_int_t    v;
    my_struct_t s;
    always_comb begin
        v       = in_val;
        s.val   = v;
        out_val = s.val;
    end
endmodule
module fixed_unpacked_demo (
    input  logic [3:0] sel,
    output logic [7:0] data_out
);
    bit [0:3][7:0] array2d;
    assign data_out = array2d[sel];
endmodule
