module ClassFeatureModule (
    input logic         enable_i,
    output logic [7:0]  status_o
);
    class MyBaseClass;
        int         m_base_int;
        logic [63:0] m_base_wide_vec;
        string      m_base_str;
        real        m_base_real;
        function new();
            m_base_int = 10;
            m_base_wide_vec = 64'hFACE_BEEF_CAFE_0001;
            m_base_str = "HelloBase";
            m_base_real = 1.234;
        endfunction
    endclass
    class MyDerivedClass extends MyBaseClass;
        byte        m_derived_byte;
        logic [127:0] m_derived_super_wide_vec;
        function new();
            super.new();
            m_derived_byte = 8'hAB;
            m_derived_super_wide_vec = 128'hDEAD_BEEF_1234_5678_ABCD_EF01_2345_6789;
        endfunction
    endclass
    MyBaseClass     base_inst;
    MyDerivedClass  derived_inst;
    always_comb begin
        if (enable_i) begin
            if (base_inst == null) begin
                base_inst = new();
            end
            if (derived_inst == null) begin
                derived_inst = new();
            end
            status_o = base_inst.m_base_int[7:0] + derived_inst.m_derived_byte;
            status_o = status_o + derived_inst.m_derived_super_wide_vec[7:0];
        end else begin
            status_o = 8'h00;
        end
    end
endmodule
module StructUnionFeatureModule (
    input logic          process_en_i,
    output logic [15:0]  data_out_o
);
    typedef struct {
        int         s_int_field;
        logic [63:0] s_wide_field;
        bit         s_bit_field;
        string      s_str_field;
    } MyUnpackedStructType;
    typedef union {
        longint     u_longint_field;
        logic [255:0] u_super_wide_field;
        byte        u_byte_field;
    } MyUnpackedUnionType;
    MyUnpackedStructType struct_var;
    MyUnpackedUnionType union_var;
    always_comb begin
        if (process_en_i) begin
            struct_var.s_int_field = 20;
            struct_var.s_wide_field = 64'h1234_5678_ABCD_EFAB;
            struct_var.s_bit_field = 1'b1;
            struct_var.s_str_field = "StructValue";
            union_var.u_longint_field = 64'hABCDEF0123456789;
            union_var.u_byte_field = 8'hFF;
            data_out_o = struct_var.s_int_field[15:0] + union_var.u_byte_field;
            data_out_o = data_out_o + struct_var.s_wide_field[15:0];
        end else begin
            data_out_o = 16'h0000;
        end
    end
endmodule
module InterfaceFeatureModule (
    input logic  clk_i,
    input logic  reset_n_i,
    input logic [7:0]  input_data_i,
    output logic [7:0] output_data_o
);
    interface MySimpleInterface;
        logic clk;
        logic rst_n;
        logic [7:0] data_in;
        logic [7:0] data_out;
    endinterface
    MySimpleInterface my_if();
    always_comb begin
        my_if.clk     = clk_i;
        my_if.rst_n   = reset_n_i;
        my_if.data_in = input_data_i;
        my_if.data_out = my_if.data_in + 1;
        output_data_o = my_if.data_out;
    end
endmodule
module AdvancedTypesModule (
    input logic          control_i,
    output logic [31:0]  result_o
);
    typedef enum logic [1:0] {
        STATE_IDLE = 2'b00,
        STATE_ACTIVE = 2'b01,
        STATE_DONE = 2'b10
    } my_state_e;
    class ComplexClass;
        int m_id;
        my_state_e m_current_state;
        bit [15:0] m_data_array [2];
        logic [3:0] m_small_vec;
        integer m_count;
        time m_timestamp;
        function new(int id_val);
            m_id = id_val;
            m_current_state = STATE_IDLE;
            m_data_array[0] = 16'hABCD;
            m_data_array[1] = 16'hEF01;
            m_small_vec = 4'b1010;
            m_count = 100;
            m_timestamp = 1000ns;
        endfunction
    endclass
    ComplexClass complex_inst;
    always_comb begin
        if (control_i) begin
            if (complex_inst == null) begin
                complex_inst = new(5);
            end
            complex_inst.m_current_state = STATE_ACTIVE;
            complex_inst.m_small_vec = complex_inst.m_small_vec + 1;
            complex_inst.m_count = complex_inst.m_count + 1;
            complex_inst.m_timestamp = complex_inst.m_timestamp + 10ps;
            result_o = complex_inst.m_id + complex_inst.m_small_vec + complex_inst.m_count + complex_inst.m_data_array[0];
        end else begin
            result_o = 32'h0;
        end
    end
endmodule
