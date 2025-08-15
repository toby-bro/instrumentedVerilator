module ArithmeticLogicalOps (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic [1:0] in_sel,
    input real in_r1,
    input real in_r2,
    output logic [15:0] out_wide_result,
    output int out_int_result,
    output real out_real_result,
    output bit out_bool_result
);
    logic [15:0] wide_a = {8'h0, in_a};
    logic [15:0] wide_b = {8'h0, in_b};
    int int_a = in_a;
    int int_b = in_b;
    always_comb begin
        case (in_sel)
            2'b00: begin
                out_int_result = int_a + int_b;
                out_wide_result = wide_a * wide_b;
                out_bool_result = (int_a % 2) & (int_b | 1);
            end
            2'b01: begin
                out_bool_result = (int_a > int_b) || (wide_a <= wide_b);
                out_int_result = (int_a << 2) >>> 1;
                out_wide_result = wide_a ^ wide_b;
            end
            2'b10: begin
                out_int_result = ~int_a;
                out_bool_result = !(int_a == int_b) ? (in_r1 < in_r2) : (in_r1 >= in_r2);
                out_wide_result = (wide_a == wide_b) ? wide_a : wide_b;
            end
            default: begin
                out_int_result = int_a / 3;
                out_wide_result = wide_a - wide_b;
                out_bool_result = (int_a != int_b) && (in_r1 != in_r2);
            end
        endcase
        out_real_result = (in_r1 + in_r2) / 2.0;
    end
endmodule
module DisplayFormatTests (
    input int d_val,
    input logic [63:0] l_val,
    input string s_val_in,
    input real r_val,
    input bit c_val_bit,
    input logic [15:0] wide_char_val,
    output string s_format_out,
    output int sscan_val_out
);
    string local_string_var;
    int    local_int_var;
    real   local_real_var;
    time   current_time_val;
    logic [31:0] packed_str_val = 32'hFEEDFACE;
    class MyDummyClass;
        int member_i;
        string member_s;
        function new(int val);
            member_i = val;
            member_s = "DummyString";
        endfunction
    endclass
    MyDummyClass dummy_obj_h;
    typedef struct packed {
        logic [7:0] field1;
        int         field2;
    } MyPackedStruct;
    typedef union {
        int         u_int;
        real        u_real;
    } MyUnion;
    MyPackedStruct local_struct;
    MyUnion local_union;
    always_comb begin
        dummy_obj_h = new(d_val);
        dummy_obj_h.member_i = d_val;
        local_struct.field1 = d_val[7:0];
        local_struct.field2 = d_val;
        local_union.u_int = d_val;
        $display("D: d=%d, h=%h, b=%b, o=%o", d_val, d_val, d_val, d_val);
        $write("W: l=%0d, l_h=%0h, l_b=%0b", l_val, l_val, l_val);
        $display("C: c_bit=%c, c_wide=%c, s=%s", c_val_bit, wide_char_val, s_val_in);
        current_time_val = $realtime;
        $display("T: time=%t", current_time_val);
        $display("M: module_name=%m");
        $display("P: percent=%%");
        $display("S: ignored_arg=%*d", 5, d_val);
        $display("SD: signed_d=%~", $signed(d_val));
        $display("PS: packed_str=%@", packed_str_val);
        $display("PT: dummy_obj_ptr=%p", dummy_obj_h);
        $display("R: r_e=%e, r_f=%f, r_g=%g, r_realtime=%^", r_val, r_val, r_val, $realtime);
        $display("V: d_val_v=%v", d_val);
        $display("UZ: u=%u, z=%z", 4'b10xz, 4'b11zx);
        $display("L: location=%l");
        $sformatf(s_format_out, "SF: d=%0d, s=%s, r=%f", d_val, s_val_in, r_val);
        sscan_val_out = $sscanf(s_val_in, "%d", local_int_var);
        sscan_val_out = local_int_var;
    end
endmodule
module DPI_C_Integration (
    input int dpi_data_in,
    input bit dpi_trigger,
    output int dpi_data_out,
    output string dpi_string_out
);
    import "DPI-C" function int my_simple_dpi_func(int arg);
    import "DPI-C" context function void my_context_dpi_func();
    import "DPI-C" function string get_dpi_string();
    int local_dpi_result;
    always_comb begin
        if (dpi_trigger) begin
            local_dpi_result = my_simple_dpi_func(dpi_data_in);
            my_context_dpi_func();
            dpi_string_out = get_dpi_string();
        end else begin
            local_dpi_result = 0;
            dpi_string_out = "";
        end
        dpi_data_out = local_dpi_result;
    end
endmodule
module DataStructureAccess (
    input int struct_in_val,
    input int union_in_val,
    input int class_in_val,
    output int struct_out_val,
    output int union_out_val,
    output int class_out_val
);
    typedef struct {
        int field1_s;
        logic [7:0] field2_s;
    } MyNestedStruct;
    MyNestedStruct local_struct_inst;
    typedef union {
        int u_int_val;
        real u_real_val;
    } MyUnionInst;
    MyUnionInst local_union_inst;
    class MyDataClass;
        int class_member_i;
        string class_member_s;
        MyNestedStruct class_nested_struct;
        MyUnionInst class_nested_union;
        function new(int val);
            class_member_i = val;
            class_member_s = "Default";
            class_nested_struct.field1_s = val + 1;
            class_nested_struct.field2_s = val[7:0] + 2;
            class_nested_union.u_int_val = val + 3;
        endfunction
    endclass
    MyDataClass local_class_h;
    always_comb begin
        local_class_h = new(class_in_val);
        local_struct_inst.field1_s = struct_in_val;
        local_struct_inst.field2_s = struct_in_val[7:0];
        struct_out_val = local_struct_inst.field1_s + local_struct_inst.field2_s;
        local_union_inst.u_int_val = union_in_val;
        union_out_val = local_union_inst.u_int_val;
        local_class_h.class_member_i = class_in_val;
        local_class_h.class_member_s = "Updated";
        local_class_h.class_nested_struct.field1_s = class_in_val * 2;
        local_class_h.class_nested_union.u_int_val = class_in_val * 3;
        class_out_val = local_class_h.class_member_i +
                        local_class_h.class_nested_struct.field1_s +
                        local_class_h.class_nested_union.u_int_val;
    end
endmodule
module TypeConversionModule (
    input logic [63:0] packed_vec_in,
    input logic [31:0] stream_val_in,
    input int array_size,
    input logic [63:0] packed_array_in_64,
    output string packed_to_str_out,
    output int wide_array_sum_out,
    output logic [7:0] unpacked_array_out_byte,
    output logic [15:0] conv_wide_array_out
);
    string temp_sformatf_str;
    string temp_stream_str;
    logic [7:0] my_unpacked_array_8_byte [0:7];
    logic [31:0] my_wide_array_unpacked [0:15];
    logic [7:0] stream_val_bytes [0:3];
    logic [15:0] conv_unpacked_array [0:3];
    always_comb begin
        temp_sformatf_str = $sformatf("%s", packed_vec_in);
        packed_to_str_out = temp_sformatf_str;
        {<<8 {stream_val_bytes}} = stream_val_in;
        temp_stream_str = $sformatf("%s", stream_val_bytes);
        packed_to_str_out = {packed_to_str_out, temp_stream_str};
        my_unpacked_array_8_byte = packed_array_in_64;
        unpacked_array_out_byte = my_unpacked_array_8_byte[0];
        conv_unpacked_array = packed_array_in_64;
        conv_wide_array_out = conv_unpacked_array[0];
        for (int i = 0; i < 16; i++) begin
            my_wide_array_unpacked[i] = i;
        end
        wide_array_sum_out = 0;
        for (int i = 0; i < 16; i++) begin
            wide_array_sum_out = wide_array_sum_out + my_wide_array_unpacked[i];
        end
    end
endmodule
module VariableInitializationTests (
    input bit clk_in,
    input int array_size_in,
    output int param_out,
    output logic [63:0] random_val_out,
    output real real_val_out,
    output string string_val_out,
    output int assoc_array_sum_out,
    output int dyn_array_sum_out,
    output int queue_sum_out,
    output int struct_member_out
);
    parameter int PARAM_INT = 123;
    parameter logic [7:0] PARAM_BYTE = 8'hFF;
    parameter longint PARAM_LONG = 64'd1_000_000_000_000;
    parameter logic [127:0] PARAM_WIDE = 128'hDEADBEEF_CAFEBABE_12345678_9ABCDEF0;
    parameter real PARAM_REAL = 3.14159;
    parameter real PARAM_INF = $inf;
    parameter real PARAM_NAN = $nan;
    parameter string PARAM_STRING = "Hello, Verilator!";
    int _default_int_val;
    logic [63:0] _large_rand_vec;
    logic [31:0] _x_temp_var_test;
    string dynamic_string_var = "Initial string";
    logic [7:0] unpacked_arr_fixed_size [0:3] = '{0: 8'hAA, 2: 8'hBB, default: 8'hCC};
    int dynamic_arr [];
    int assoc_arr [string];
    int assoc_arr_int_key [int];
    int my_queue [$];
    typedef struct {
        int s_field1;
        real s_field2;
        logic [15:0] s_field3;
    } MyTestStruct;
    MyTestStruct nested_struct_var;
    class MyResetClass;
        int val;
        function new();
            val = 0;
        endfunction
    endclass
    MyResetClass my_class_handle;
    always_comb begin
        param_out = PARAM_INT + PARAM_BYTE;
        real_val_out = PARAM_REAL + PARAM_INF + PARAM_NAN;
        string_val_out = PARAM_STRING;
        random_val_out = _large_rand_vec + _default_int_val + _x_temp_var_test;
        dynamic_arr = new[array_size_in];
        for (int i = 0; i < dynamic_arr.size(); i++) begin
            dynamic_arr[i] = i;
        end
        assoc_arr["one"] = 1;
        assoc_arr["two"] = 2;
        assoc_arr_int_key[10] = 100;
        assoc_arr_int_key[20] = 200;
        my_queue.push_back(10);
        my_queue.push_back(20);
        assoc_array_sum_out = 0;
        foreach (assoc_arr[key]) assoc_array_sum_out += assoc_arr[key];
        foreach (assoc_arr_int_key[key]) assoc_array_sum_out += assoc_arr_int_key[key];
        dyn_array_sum_out = 0;
        foreach (dynamic_arr[idx]) dyn_array_sum_out += dynamic_arr[idx];
        queue_sum_out = 0;
        foreach (my_queue[idx]) queue_sum_out += my_queue[idx];
        nested_struct_var.s_field1 = 100;
        nested_struct_var.s_field2 = 12.34;
        nested_struct_var.s_field3 = 16'hAAAA;
        struct_member_out = nested_struct_var.s_field1 + nested_struct_var.s_field3;
        my_class_handle = new();
        my_class_handle.val = 5;
    end
endmodule
