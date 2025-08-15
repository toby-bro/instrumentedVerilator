module ClassFeatureModule (
    input logic [7:0] in_data,
    output logic [7:0] out_result
);
virtual class MyInterfaceBase;
    pure virtual function int get_value();
    pure virtual function int get_placeholder_value();
endclass : MyInterfaceBase
class BaseClass extends MyInterfaceBase;
    static int base_static_var = 10;
    parameter BASE_PARAM = 5;
    function new();
    endfunction
    virtual function int get_value();
        return base_static_var;
    endfunction
    virtual function int get_placeholder_value();
        return BASE_PARAM;
    endfunction
    virtual function int calculate(int val);
        return val + BASE_PARAM;
    endfunction
    static function int get_base_static_var();
        return base_static_var;
    endfunction
    static task set_base_static_var(int val);
        base_static_var = val;
    endtask
endclass : BaseClass
class DerivedClass extends BaseClass;
    static int derived_static_var = 30;
    function new();
        super.new();
    endfunction
    virtual function int calculate(int val);
        return val * 2 + super.calculate(val);
    endfunction
    virtual function int get_value();
        return derived_static_var + super.get_value();
    endfunction
    static function int get_derived_static_var();
        return derived_static_var;
    endfunction
endclass : DerivedClass
DerivedClass dc_inst;
logic [7:0] local_result;
always_comb begin
    if (dc_inst == null) begin
        dc_inst = new();
    end
    BaseClass::set_base_static_var(in_data);
    local_result = BaseClass::get_base_static_var() +
                   DerivedClass::get_derived_static_var() +
                   dc_inst.calculate(in_data[3:0]);
    out_result = local_result;
end
endmodule : ClassFeatureModule
module DataTypesAndDPI (
    input logic [15:0] in_value,
    output logic [15:0] out_processed_value
);
    import "DPI-C" function int dpi_process_data(int data);
    typedef struct packed {
        logic [7:0] field_a;
        struct packed {
            logic [3:0] sub_field_x;
            logic [3:0] sub_field_y;
        } sub_struct;
        logic [7:0] field_b;
    } my_packed_struct_t;
    typedef union packed {
        logic [15:0] word;
        struct {
            logic [7:0] lo;
            logic [7:0] hi;
        } bytes;
    } my_packed_union_t;
    class InitialContainer;
        public typedef struct packed {
            logic [3:0] public_data;
            logic [3:0] public_flag;
        } public_struct_t;
        int class_local_var = 0;
        int dpi_result = 0;
        public_struct_t pub_data;
        function new(int init_val);
            pub_data.public_data = 0;
            pub_data.public_flag = 0;
            class_local_var = 100;
            dpi_result = dpi_process_data(init_val);
            pub_data.public_data = init_val[3:0];
        endfunction
    endclass : InitialContainer
    InitialContainer ic_inst;
    my_packed_struct_t s_var;
    my_packed_union_t u_var;
    always_comb begin
        if (ic_inst == null) begin
            ic_inst = new(in_value);
        end
        s_var.field_a = in_value[7:0];
        s_var.sub_struct.sub_field_x = in_value[11:8];
        s_var.sub_struct.sub_field_y = in_value[15:12];
        u_var.word = in_value;
        out_processed_value = dpi_process_data(in_value);
        if (ic_inst != null) begin
            out_processed_value = out_processed_value + ic_inst.class_local_var + ic_inst.dpi_result + ic_inst.pub_data.public_data;
        end
    end
endmodule : DataTypesAndDPI
module SimpleModule (
    input logic [3:0] in_a,
    output logic [3:0] out_b
);
    parameter MOD_PARAM_WIDTH = 4;
    logic [MOD_PARAM_WIDTH-1:0] internal_reg;
    initial begin
        internal_reg = 0;
    end
    always_comb begin
        internal_reg = in_a + 1;
        out_b = internal_reg;
    end
endmodule : SimpleModule
module ClassMembersModule (
    input logic [7:0] in_data,
    output logic [7:0] out_status
);
    class MemberTestClass;
        static int s_counter = 0;
        parameter int LOCAL_OFFSET = 5;
        function new();
            s_counter++;
        endfunction
        function int get_offset_value(int val);
            return val + LOCAL_OFFSET;
        endfunction
        static function int get_static_count();
            return s_counter;
        endfunction
        static task reset_counter();
            s_counter = 0;
        endtask
    endclass
    MemberTestClass mt_inst;
    logic [7:0] temp_val;
    always_comb begin
        if (mt_inst == null) begin
            mt_inst = new();
        end
        MemberTestClass::reset_counter();
        temp_val = MemberTestClass::get_static_count() + mt_inst.get_offset_value(in_data[3:0]);
        out_status = temp_val;
    end
endmodule : ClassMembersModule
module InitialModule (
    input logic in_trigger,
    output logic out_status
);
    static logic static_flag_reg;
    initial begin
        static_flag_reg = 1'b1;
    end
    always_comb begin
        out_status = static_flag_reg & in_trigger;
    end
endmodule
