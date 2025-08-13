module slice_array_assign(
    input  logic [7:0] in_data,
    input  logic       sel,
    output logic [7:0] out_data
);
    logic [7:0] array_asc  [0:3];
    logic [7:0] array_desc [3:0];
    logic [7:0] tmp        [0:3];
    always_comb begin
        array_desc = '{3: in_data, 2: in_data, 1: in_data, 0: in_data};
        array_asc  = array_desc;
        tmp        = array_asc;
        out_data   = tmp[sel ? 2 : 1];
    end
endmodule
module array_equality(
    input  logic [7:0] data0,
    input  logic [7:0] data1,
    output logic       equal
);
    logic [7:0] arr0 [0:3];
    logic [7:0] arr1 [0:3];
    always_comb begin
        arr0  = '{default: data0};
        arr1  = '{default: data1};
        equal = (arr0 == arr1);
    end
endmodule
module array_wildcard_eq(
    input  logic [7:0] data0,
    input  logic [7:0] data1,
    output logic       match
);
    logic [7:0] arr0 [0:3];
    logic [7:0] arr1 [0:3];
    logic [31:0] packed0;
    logic [31:0] packed1;
    always_comb begin
        arr0    = '{default: data0};
        arr1    = '{default: data1};
        packed0 = {arr0[3], arr0[2], arr0[1], arr0[0]};
        packed1 = {arr1[3], arr1[2], arr1[1], arr1[0]};
        match   = (packed0 ==? packed1);
    end
endmodule
module array_wildcard_neq(
    input  logic [7:0] data0,
    input  logic [7:0] data1,
    output logic       mismatch
);
    logic [7:0] arr0 [0:3];
    logic [7:0] arr1 [0:3];
    logic [31:0] packed0;
    logic [31:0] packed1;
    always_comb begin
        arr0     = '{default: data0};
        arr1     = '{default: data1};
        packed0  = {arr0[3], arr0[2], arr0[1], arr0[0]};
        packed1  = {arr1[3], arr1[2], arr1[1], arr1[0]};
        mismatch = (packed0 !=? packed1);
    end
endmodule
module struct_pattern(
    input  logic [3:0] in_a,
    input  logic [3:0] in_b,
    output logic [7:0] out_word
);
    typedef struct packed {
        logic [3:0] a;
        logic [3:0] b;
    } pair_t;
    pair_t packed_data;
    always_comb begin
        packed_data = '{a: in_a, b: in_b};
        out_word    = {packed_data.a, packed_data.b};
    end
endmodule
module init_array_slice(
    input  logic [1:0] sel,
    output logic [7:0] element
);
    logic [7:0] const_arr [0:3] = '{8'hAA, 8'hBB, 8'hCC, 8'hDD};
    always_comb begin
        element = const_arr[sel];
    end
endmodule
module packed_slice_select(
    input  logic [31:0] in_word,
    output logic [15:0] upper_half
);
    always_comb begin
        upper_half = in_word[31:16];
    end
endmodule
