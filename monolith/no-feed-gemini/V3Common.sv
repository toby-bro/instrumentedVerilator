package MySharedTypes;
    typedef struct {
        logic [31:0] id;
        string name;
        real value;
        logic [127:0] wide_data;
    } MyUnpackedStruct;
    typedef union {
        logic [63:0] data_wide;
        int data_int;
        real data_real;
        bit [15:0] flags;
    } MyUnpackedUnion;
    class MyBaseClass;
        int val_int_base;
        logic [63:0] val_wide_base;
        string name_base;
        function new(int init_int, logic [63:0] init_wide, string base_name_in);
            this.val_int_base = init_int;
            this.val_wide_base = init_wide;
            this.name_base = base_name_in;
        endfunction
    endclass
    class MyDerivedClass extends MyBaseClass;
        string val_str_derived;
        real val_real_derived;
        MyUnpackedStruct derived_struct_member;
        function new(string init_str, int init_int, logic [63:0] init_wide, MyUnpackedStruct init_struct);
            super.new(init_int, init_wide, {init_str, "_base"});
            this.val_str_derived = init_str;
            this.val_real_derived = init_int * 1.0;
            this.derived_struct_member = init_struct;
        endfunction
    endclass
endpackage
import MySharedTypes::*;
interface SvSimpleInterface (
    input logic clk_i
);
    logic reset_n;
    logic [7:0] data_bus;
    logic valid;
    modport Master (output reset_n, output data_bus, output valid, input clk_i);
    modport Slave (input reset_n, input data_bus, input valid, input clk_i);
endinterface
module SvBasicTypesModule (
    input logic in_logic_a,
    input int in_int_b,
    input real in_real_c,
    input string in_string_d,
    output logic out_logic_e,
    output int out_int_f,
    output real out_real_g,
    output string out_string_h
);
    logic internal_logic;
    int internal_int;
    real internal_real;
    string internal_string = "initial_basic_string";
    always_comb begin
        internal_logic = in_logic_a;
        internal_int = in_int_b + 5;
        internal_real = in_real_c * 2.5;
        internal_string = in_string_d;
        out_logic_e = internal_logic;
        out_int_f = internal_int;
        out_real_g = internal_real;
        out_string_h = internal_string;
    end
endmodule
module SvWideVectorModule (
    input logic [255:0] in_wide_logic_a,
    input bit [127:0] in_wide_bit_b,
    output logic [255:0] out_wide_logic_c,
    output bit [127:0] out_wide_bit_d
);
    logic [511:0] internal_wide_var;
    bit [63:0] small_wide_var;
    always_comb begin
        internal_wide_var = {in_wide_logic_a, in_wide_bit_b};
        small_wide_var = in_wide_logic_a[63:0] ^ in_wide_bit_b[63:0];
        out_wide_logic_c = internal_wide_var[255:0] + in_wide_logic_a;
        out_wide_bit_d = small_wide_var;
    end
endmodule
module SvStructUnionModule (
    input MyUnpackedStruct in_struct_val,
    input MyUnpackedUnion in_union_val,
    output MyUnpackedStruct out_struct_res,
    output MyUnpackedUnion out_union_res
);
    MyUnpackedStruct module_level_struct;
    MyUnpackedUnion module_level_union;
    always_comb begin
        module_level_struct.id = in_struct_val.id + 1;
        module_level_struct.name = {in_struct_val.name, "_suffix"};
        module_level_struct.value = in_struct_val.value * 10.0;
        module_level_struct.wide_data = in_struct_val.wide_data + 1;
        module_level_union.data_int = in_union_val.data_int * 2;
        module_level_union.data_real = in_union_val.data_real + 1.0;
        module_level_union.data_wide = in_union_val.data_wide;
        module_level_union.flags = in_union_val.flags;
        out_struct_res = module_level_struct;
        out_union_res = module_level_union;
    end
endmodule
module SvClassUsageModule (
    input logic enable_class_op,
    input int data_in,
    output int class_result,
    output logic [63:0] wide_class_result
);
    MyBaseClass   base_obj_handle;
    MyDerivedClass derived_obj_handle;
    always_comb begin
        class_result = 0;
        wide_class_result = 0;
        if (enable_class_op) begin
            MyUnpackedStruct temp_struct;
            temp_struct.id = data_in;
            temp_struct.name = "DerivedStruct";
            temp_struct.value = data_in * 0.1;
            temp_struct.wide_data = {data_in[63:0], data_in[63:0]} + 1;
            base_obj_handle = new(data_in, data_in * 2, "BaseInst");
            derived_obj_handle = new("DerivedInst", data_in + 1, {data_in[63:0], data_in[63:0]} * 3, temp_struct);
            class_result = base_obj_handle.val_int_base + derived_obj_handle.val_int_base;
            wide_class_result = base_obj_handle.val_wide_base + derived_obj_handle.val_wide_base;
            derived_obj_handle.val_str_derived = {derived_obj_handle.val_str_derived, "_modified"};
            derived_obj_handle.val_real_derived = derived_obj_handle.val_real_derived + 0.5;
            derived_obj_handle.derived_struct_member.id = derived_obj_handle.derived_struct_member.id + 10;
        end
    end
endmodule
