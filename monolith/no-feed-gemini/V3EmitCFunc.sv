module ArithmeticLogicalBitwiseOperators (
    input logic [63:0] in_a, in_b,
    input logic [7:0] in_c, in_d,
    input bit in_sel,
    output logic [63:0] out_arith_wide,
    output logic [63:0] out_logic_wide,
    output logic [63:0] out_bitwise_wide,
    output logic [7:0] out_arith_narrow,
    output logic [7:0] out_logic_narrow,
    output logic [7:0] out_bitwise_narrow,
    output logic [7:0] out_conditional
);
    always_comb begin
        out_arith_wide = in_a + in_b - (in_a * in_b) / 2 + (in_a % 100); 
        out_logic_wide = (in_a == in_b) && (in_a != 0) || (in_b > in_a) && (in_b <= in_a + 1); 
        out_bitwise_wide = (in_a & in_b) | (in_a ^ in_b) ~ (in_b << 2) >> 1 <<< 3 >>> 4; 
    end
    always_comb begin
        out_arith_narrow = in_c + in_d - (in_c * in_d) / 2 + (in_c % 50); 
        out_logic_narrow = (in_c == in_d) && (in_c != 0) || (in_d > in_c) && (in_d <= in_c + 1); 
        out_bitwise_narrow = (in_c & in_d) | (in_c ^ in_d) ~ (in_d << 1) >> 1; 
    end
    always_comb begin
        out_conditional = in_sel ? in_c : in_d; 
    end
endmodule
module ComplexDataTypesAndResets (
    input logic [3:0] in_idx,
    input string in_initial_str,
    input real in_real_val, 
    output logic [7:0] out_unpacked_arr_val,
    output int out_assoc_arr_val,
    output string out_struct_str_val,
    output real out_union_real_val,
    output int out_rand_val
);
    localparam int PARAM_INT = 100;
    localparam logic [15:0] PARAM_WIDE = 16'hFEED;
    logic [7:0] unpacked_arr[4];
    int assoc_arr[string];
    logic [3:0] dyn_arr[];
    int int_queue[$];
    typedef struct packed {
        logic [3:0] f1;
        logic [3:0] f2;
        logic [63:0] f_wide; 
    } packed_s;
    packed_s ps_var;
    typedef struct {
        int x;
        string y;
    } unpacked_s;
    unpacked_s us_var;
    typedef union {
        int i;
        real r;
    } unpacked_u;
    unpacked_u uu_var;
    string my_string;
    rand int r_val;
    randc bit [15:0] rc_val;
    logic _x_init_signal;
    always_comb begin
        unpacked_arr[0] = 8'hAA;
        unpacked_arr[1] = 8'hBB;
        unpacked_arr[2] = 8'hCC;
        unpacked_arr[3] = 8'hDD;
        out_unpacked_arr_val = unpacked_arr[in_idx % 4];
        assoc_arr["key1"] = 123;
        assoc_arr["key2"] = 456;
        assoc_arr[in_initial_str] = PARAM_INT; 
        if (assoc_arr.exists(in_initial_str)) begin
            out_assoc_arr_val = assoc_arr[in_initial_str];
        end else begin
            out_assoc_arr_val = 0;
        end
        dyn_arr = new[2];
        dyn_arr[0] = 4'b0101;
        dyn_arr[1] = 4'b1010;
        int_queue.push_back(789);
        int_queue.push_front(987);
        ps_var.f1 = in_idx;
        ps_var.f2 = 4'hF;
        ps_var.f_wide = PARAM_WIDE; 
        us_var.x = in_idx * 10;
        my_string = in_initial_str; 
        us_var.y = my_string;
        out_struct_str_val = us_var.y;
        uu_var.r = in_real_val + 1.0;
        out_union_real_val = uu_var.r;
        void' (r_val.randomize());
        void' (rc_val.randomize());
        out_rand_val = r_val;
        _x_init_signal = 1'b0; 
    end
endmodule
module SystemTasksAndClasses (
    input int in_c_arg,
    input real in_real_val,
    input string in_format_str,
    input logic [7:0] in_char_val,
    output string out_sformat_result,
    output int out_c_ret_val,
    output int out_class_member_val
);
    timeunit 1ns;
    timeprecision 1ps;
    interface MyInterface ();
        logic clk;
        logic rst;
        modport dut (input clk, input rst);
    endinterface
    class MyClass;
        int member_var;
        virtual MyInterface iface_ref;
        function new();
            member_var = 0;
            iface_ref = null; 
        endfunction
        function void set_member(int val);
            member_var = val;
        endfunction
        function int get_member();
            return member_var;
        endfunction
        function automatic void C_method(int val);
            member_var = val + 1;
        endfunction
    endclass
    import "DPI-C" function void c_function(int arg1, string arg2);
    import "DPI-C" function int c_return_function(real arg);
    MyClass my_object;
    always_comb begin
        my_object = new();
        my_object.set_member(in_c_arg);
        out_class_member_val = my_object.get_member();
        my_object.C_method(in_c_arg + 10);
        c_function(in_c_arg, "Hello from SV via DPI-C");
        out_c_ret_val = c_return_function(in_real_val);
        string temp_sformat;
        logic [63:0] wide_val = {in_c_arg, 32'hFEEDFACE};
        real time_val = $realtime;
        string null_str_var;
        int dummy_ptr_val = 1; 
        void *void_ptr_val = null; 
        logic [31:0] four_state_val = 32'h01XZ_01XZ; 
        temp_sformat = $sformatf(
            "Int: %d, Hex: %h, Bin: %b, Oct: %o, Char: %c, Str: %s, Real: %f, Exp: %e, Gen: %g, Time: %t, Wide: %0d, Ptr_int: %p, Fs_val: %v, Signed: %~, Packed_str: %@, Ignored: %*d, Scope: %m",
            in_c_arg, wide_val, wide_val, wide_val, in_char_val, in_format_str,
            in_real_val, in_real_val, in_real_val, time_val, wide_val, dummy_ptr_val, four_state_val, -in_c_arg,
            in_format_str, 
            in_c_arg, 
            1 
        );
        out_sformat_result = temp_sformat;
        temp_sformat = $sformatf("Null String: %s", null_str_var);
        out_sformat_result = {out_sformat_result, " | ", temp_sformat};
        logic [8192:0] large_width_signal; 
        large_width_signal = 0;
        temp_sformat = $sformatf("Large width value: %h", large_width_signal);
        out_sformat_result = {out_sformat_result, " | ", temp_sformat};
    end
endmodule
module ConstantExpressionsAndConversions (
    input logic [127:0] in_wide_data,
    input string in_string_val,
    output logic [127:0] out_wide_const,
    output string out_packed_str,
    output logic [7:0] out_cvt_array_val,
    output real out_real_const,
    output longint unsigned out_quad_const
);
    logic [127:0] wide_target;
    real real_target;
    longint unsigned quad_target;
    string string_target;
    logic [3:0] four_state_target; 
    typedef struct packed { logic [31:0] val1; logic [31:0] val2; logic [31:0] val3; logic [31:0] val4; } large_p_struct_t;
    large_p_struct_t large_packed_struct;
    logic [15:0] wide_array_in [4]; 
    class MyClass;
        function new(); endfunction
    endclass
    MyClass local_class_handle; 
    always_comb begin
        out_wide_const = 128'hFFFF_FFFF_FFFF_FFFF_AAAA_AAAA_AAAA_AAAA;
        wide_target = 128'h1234_5678_9ABC_DEF0_FEED_BEEF_C0DE_FACE; 
        real_target = 3.14159265358979323846; 
        out_real_const = real_target;
        real_target = 1.0/0.0; 
        real_target = 0.0/0.0; 
        quad_target = 64'hFEDCBA9876543210;
        out_quad_const = quad_target;
        string_target = "This is a constant string for emitConstantString coverage.";
        out_packed_str = string_target; 
        four_state_target = 4'b01XZ;
        local_class_handle = null; 
        large_packed_struct.val1 = 32'h1111_2222;
        large_packed_struct.val2 = 32'h3333_4444;
        large_packed_struct.val3 = 32'h5555_6666;
        large_packed_struct.val4 = 32'h7777_8888;
        out_packed_str = $sformatf("%p", large_packed_struct); 
        wide_array_in[0] = in_wide_data[15:0];
        wide_array_in[1] = in_wide_data[31:16];
        wide_array_in[2] = in_wide_data[47:32];
        wide_array_in[3] = in_wide_data[63:48];
        out_cvt_array_val = wide_array_in[0][7:0]; 
    end
endmodule
