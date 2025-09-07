module ScalarAndStringConstants (
    input bit clk_i,
    input int in_val_i,
    output longint out_val_o
);
    const int C_INT_VAL = 12345;
    const logic C_LOGIC_BIT = 1'b1;
    const bit C_BIT_VAL = 1'b0;
    const byte C_BYTE_VAL = 8'hFF;
    const shortint C_SHORTINT_VAL = 32767;
    const longint C_LONGINT_VAL = 64'd9876543210;
    const real C_REAL_VAL = 3.14159265;
    const shortreal C_SHORTREAL_VAL = 2.71828;
    const time C_TIME_VAL = 100ns;
    const string C_STRING_MSG = "Hello Verilator Constant Pool! This is a longer string to influence file size calculations.";
    typedef enum {
        RED,
        GREEN,
        BLUE,
        YELLOW,
        CYAN,
        MAGENTA
    } Color_t;
    const Color_t C_DEFAULT_COLOR = GREEN;
    const Color_t C_ANOTHER_COLOR = MAGENTA;
    const int LP_CALC_VAL = C_INT_VAL + 5;
    parameter P_FACTOR = 10;
    parameter P_OFFSET = 20;
    assign out_val_o = C_LONGINT_VAL + LP_CALC_VAL * P_FACTOR + in_val_i + P_OFFSET;
    always_comb begin
        automatic int temp_int_val;
        automatic logic temp_logic_bit;
        automatic bit temp_bit_val;
        automatic byte temp_byte_val;
        automatic shortint temp_shortint_val;
        automatic real temp_real_val;
        automatic shortreal temp_shortreal_val;
        automatic time temp_time_val;
        automatic Color_t temp_color_val;
        temp_int_val = C_INT_VAL;
        temp_logic_bit = C_LOGIC_BIT;
        temp_bit_val = C_BIT_VAL;
        temp_byte_val = C_BYTE_VAL;
        temp_shortint_val = C_SHORTINT_VAL;
        temp_real_val = C_REAL_VAL;
        temp_shortreal_val = C_SHORTREAL_VAL;
        temp_time_val = C_TIME_VAL;
        temp_color_val = C_DEFAULT_COLOR;
        if (temp_logic_bit) begin
        end
        if (temp_bit_val) begin
        end
        if (temp_byte_val == 8'hFF) begin
        end
        if (temp_shortint_val > 0) begin
        end
        if (temp_real_val > 3.0) begin
        end
        if (temp_shortreal_val < 3.0) begin
        end
        if (temp_time_val == 100ns) begin
        end
        if (temp_color_val == BLUE) begin
        end
        if (C_ANOTHER_COLOR == YELLOW) begin
        end
    end
endmodule
module WideAndStructConstants (
    input logic [63:0] data_in_i,
    output logic [1023:0] wide_out_o
);
    const logic [255:0] C_WIDE_256_VAL = {256{1'b1}};
    const logic [1023:0] C_WIDE_1024_VAL = {512{2'b10}} ^ {512{2'b01}} + 1024'd12345;
    typedef struct packed {
        logic [7:0] field1;
        int         field2;
        bit         field3;
        logic [15:0] field4;
    } PackedStruct_t;
    const PackedStruct_t C_PACKED_STRUCT = '{
        field1: 8'hAA,
        field2: 123,
        field3: 1'b1,
        field4: 16'h55AA
    };
    typedef struct {
        string      name;
        real        value;
        logic [3:0] id;
        logic [7:0] data [2];
    } UnpackedStruct_t;
    const UnpackedStruct_t C_UNPACKED_STRUCT = '{
        name: "ConstantStruct_LongName_For_Testing_String_Lengths",
        value: 9.876,
        id: 4'hF,
        data: '{8'h11, 8'h22}
    };
    typedef union packed {
        logic [31:0] u_dword;
        logic [31:0] u_hword_view;
        logic [31:0] u_byte_view;
    } PackedUnion_t;
    const PackedUnion_t C_PACKED_UNION = '{u_dword: 32'hFEEDFACE};
    const real C_REAL_CONSTANT_FOR_UNION_TEST = 1.234;
    const logic [15:0] C_PACKED_ARRAY [4] = '{16'h1111, 16'h2222, 16'h3333, 16'h4444};
    const bit [7:0] C_PACKED_BYTE_ARRAY = 8'hBE;
    assign wide_out_o = C_WIDE_1024_VAL & {C_WIDE_256_VAL, C_WIDE_256_VAL, C_WIDE_256_VAL, C_WIDE_256_VAL} | { {960{1'b0}}, data_in_i };
    always_comb begin
        automatic logic [7:0] temp_f1 = C_PACKED_STRUCT.field1;
        automatic string temp_name = C_UNPACKED_STRUCT.name;
        automatic logic [31:0] temp_union_val = C_PACKED_UNION.u_dword;
        automatic logic [15:0] temp_arr_val = C_PACKED_ARRAY[1];
        automatic real temp_union_real = C_REAL_CONSTANT_FOR_UNION_TEST;
        automatic logic [7:0] temp_unpacked_struct_data = C_UNPACKED_STRUCT.data[0];
        if (temp_f1 == 8'hAA && temp_name == "ConstantStruct_LongName_For_Testing_String_Lengths" && temp_union_val == 32'hFEEDFACE && temp_arr_val == 16'h2222 && temp_union_real > 1.0 && temp_unpacked_struct_data == 8'h11) begin
        end
        if (C_PACKED_BYTE_ARRAY == 8'hBE) begin
        end
    end
endmodule
module UnpackedArrayConstants (
    input int index_i,
    output logic [7:0] array_element_o
);
    const logic [7:0] C_UNPACKED_BYTE_ARRAY [0:255] = '{
        8'h00, 8'h01, 8'h02, 8'h03, 8'h04, 8'h05, 8'h06, 8'h07, 8'h08, 8'h09, 8'h0A, 8'h0B, 8'h0C, 8'h0D, 8'h0E, 8'h0F,
        8'h10, 8'h11, 8'h12, 8'h13, 8'h14, 8'h15, 8'h16, 8'h17, 8'h18, 8'h19, 8'h1A, 8'h1B, 8'h1C, 8'h1D, 8'h1E, 8'h1F,
        8'h20, 8'h21, 8'h22, 8'h23, 8'h24, 8'h25, 8'h26, 8'h27, 8'h28, 8'h29, 8'h2A, 8'h2B, 8'h2C, 8'h2D, 8'h2E, 8'h2F,
        8'h30, 8'h31, 8'h32, 8'h33, 8'h34, 8'h35, 8'h36, 8'h37, 8'h38, 8'h39, 8'h3A, 8'h3B, 8'h3C, 8'h3D, 8'h3E, 8'h3F,
        8'h40, 8'h41, 8'h42, 8'h43, 8'h44, 8'h45, 8'h46, 8'h47, 8'h48, 8'h49, 8'h4A, 8'h4B, 8'h4C, 8'h4D, 8'h4E, 8'h4F,
        8'h50, 8'h51, 8'h52, 8'h53, 8'h54, 8'h55, 8'h56, 8'h57, 8'h58, 8'h59, 8'h5A, 8'h5B, 8'h5C, 8'h5D, 8'h5E, 8'h5F,
        8'h60, 8'h61, 8'h62, 8'h63, 8'h64, 8'h65, 8'h66, 8'h67, 8'h68, 8'h69, 8'h6A, 8'h6B, 8'h6C, 8'h6D, 8'h6E, 8'h6F,
        8'h70, 8'h71, 8'h72, 8'h73, 8'h74, 8'h75, 8'h76, 8'h77, 8'h78, 8'h79, 8'h7A, 8'h7B, 8'h7C, 8'h7D, 8'h7E, 8'h7F,
        8'h80, 8'h81, 8'h82, 8'h83, 8'h84, 8'h85, 8'h86, 8'h87, 8'h88, 8'h89, 8'h8A, 8'h8B, 8'h8C, 8'h8D, 8'h8E, 8'h8F,
        8'h90, 8'h91, 8'h92, 8'h93, 8'h94, 8'h95, 8'h96, 8'h97, 8'h98, 8'h99, 8'h9A, 8'h9B, 8'h9C, 8'h9D, 8'h9E, 8'h9F,
        8'hA0, 8'hA1, 8'hA2, 8'hA3, 8'hA4, 8'hA5, 8'hA6, 8'hA7, 8'hA8, 8'hA9, 8'hAA, 8'hAB, 8'hAC, 8'hAD, 8'hAE, 8'hAF,
        8'hB0, 8'hB1, 8'hB2, 8'hB3, 8'hB4, 8'hB5, 8'hB6, 8'hB7, 8'hB8, 8'hB9, 8'hBA, 8'hBB, 8'hBC, 8'hBD, 8'hBE, 8'hBF,
        8'hC0, 8'hC1, 8'hC2, 8'hC3, 8'hC4, 8'hC5, 8'hC6, 8'hC7, 8'hC8, 8'hC9, 8'hCA, 8'hCB, 8'hCC, 8'hCD, 8'hCE, 8'hCF,
        8'hD0, 8'hD1, 8'hD2, 8'hD3, 8'hD4, 8'hD5, 8'hD6, 8'hD7, 8'hD8, 8'hD9, 8'hDA, 8'hDB, 8'hDC, 8'hDD, 8'hDE, 8'hDF,
        8'hE0, 8'hE1, 8'hE2, 8'hE3, 8'hE4, 8'hE5, 8'hE6, 8'hE7, 8'hE8, 8'hE9, 8'hEA, 8'hEB, 8'hEC, 8'hED, 8'hEE, 8'hEF,
        8'hF0, 8'hF1, 8'hF2, 8'hF3, 8'hF4, 8'hF5, 8'hF6, 8'hF7, 8'hF8, 8'hF9, 8'hFA, 8'hFB, 8'hFC, 8'hFD, 8'hFE, 8'hFF
    };
    const int C_MULTI_ARRAY [3][4] = '{
        '{10, 20, 30, 40},
        '{50, 60, 70, 80},
        '{90, 100, 110, 120}
    };
    typedef struct {
        string      label;
        int         value;
        real        ratio;
    } S_Item_t;
    const S_Item_t C_ITEM_LIST [3] = '{
        '{label: "FirstItem", value: 100, ratio: 1.0},
        '{label: "SecondItem", value: 200, ratio: 2.0},
        '{label: "ThirdItem", value: 300, ratio: 3.0}
    };
    always_comb begin
        automatic int temp_multi_val;
        automatic string temp_item_label;
        automatic real temp_item_ratio;
        if (index_i >= 0 && index_i < 256) begin
            array_element_o = C_UNPACKED_BYTE_ARRAY[index_i];
        end else begin
            array_element_o = 8'hXX;
        end
        temp_multi_val = C_MULTI_ARRAY[0][0];
        temp_item_label = C_ITEM_LIST[1].label;
        temp_item_ratio = C_ITEM_LIST[2].ratio;
        if (temp_multi_val == 10 && temp_item_label == "SecondItem" && temp_item_ratio == 3.0) begin
        end
    end
endmodule
module TypeDefAndStaticConsts (
    input bit toggle_i,
    output int derived_val_o
);
    typedef logic [63:0] DataBus_t;
    typedef int IntArray_t [5];
    typedef struct {
        real x, y, z;
    } Point3D_t;
    typedef byte ByteArray_t [2];
    const DataBus_t C_DATA_BUS_VAL = 64'hFEDCBA9876543210;
    const IntArray_t C_INT_ARRAY = '{1, 2, 3, 4, 5};
    const Point3D_t C_3D_POINT = '{x: 1.0, y: 2.0, z: 3.0};
    const ByteArray_t C_BYTE_ARRAY_TYPEDEF = '{8'hDE, 8'hAD};
    class MyStaticAndInstanceClass;
        static const int S_CLASS_INT_VAL = 789;
        static const string S_CLASS_STR_VAL = "Static Class Constant Long String";
        static const logic [31:0] S_CLASS_WIDE_VAL = 32'hABCDEF01;
        static const real S_CLASS_REAL_VAL = 4.567;
        int m_instance_id;
        function new();
            m_instance_id = 1000;
        endfunction
    endclass
    always_comb begin
        automatic int temp_static_int = MyStaticAndInstanceClass::S_CLASS_INT_VAL;
        automatic string temp_static_str = MyStaticAndInstanceClass::S_CLASS_STR_VAL;
        automatic logic [31:0] temp_static_wide = MyStaticAndInstanceClass::S_CLASS_WIDE_VAL;
        automatic real temp_static_real = MyStaticAndInstanceClass::S_CLASS_REAL_VAL;
        automatic MyStaticAndInstanceClass my_inst = new();
        automatic int instance_specific_val = my_inst.m_instance_id;
        if (toggle_i) begin
            derived_val_o = temp_static_int + C_INT_ARRAY[0] + int'(C_3D_POINT.x) + int'(temp_static_real) + instance_specific_val;
        end else begin
            derived_val_o = temp_static_int * 2 + C_INT_ARRAY[4] + int'(C_3D_POINT.y) + int'(temp_static_real * 2) + instance_specific_val;
        end
        if (C_DATA_BUS_VAL == 64'hFEDCBA9876543210 && temp_static_str == "Static Class Constant Long String" && temp_static_wide == 32'hABCDEF01 && C_BYTE_ARRAY_TYPEDEF[0] == 8'hDE) begin
        end
    end
endmodule
