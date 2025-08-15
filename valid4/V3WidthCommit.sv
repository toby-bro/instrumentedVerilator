module m_BasicTypesAndCasting (
    input logic [7:0] in_a,
    input int         in_b,
    output int          out_sum,
    output int          out_diff,
    output int          out_cast_signed
);
    parameter P_VAL = 123;
    localparam L_VAL = 456;
    const bit [3:0] C_BITS = 4'b1010;
    logic [7:0] val_a = in_a;
    int         val_b = in_b;
    logic [15:0] unsigned_val;
    logic signed [31:0] signed_val;
    always_comb begin
        unsigned_val = P_VAL + L_VAL;
        signed_val = $signed(val_a) - $signed(val_b);
        out_sum = unsigned_val + C_BITS;
        out_diff = int'(in_a) - in_b;
        out_cast_signed = signed'(val_b);
    end
endmodule
module m_StructUnionEnumTypes (
    input  logic [7:0] in_data,
    output logic [7:0] out_struct_val,
    output logic [7:0] out_union_val,
    output int         out_enum_val,
    output logic [7:0] out_typedef_byte
);
    typedef struct packed {
        logic [7:0] field1;
        logic [3:0] field2;
    } my_struct_t;
    my_struct_t s_var;
    typedef union packed {
        logic [7:0] byte_val;
        logic [15:0] word_val;
    } my_union_t;
    my_union_t u_var;
    typedef enum {
        STATE_IDLE = 0,
        STATE_RUNNING,
        STATE_DONE
    } my_state_e;
    my_state_e current_state;
    typedef logic [7:0] byte_alias_t;
    byte_alias_t byte_var;
    always_comb begin
        s_var.field1 = in_data;
        s_var.field2 = in_data[3:0];
        out_struct_val = s_var.field1;
        u_var.byte_val = in_data;
        out_union_val = u_var.byte_val;
        current_state = STATE_RUNNING;
        if (in_data > 100) begin
            current_state = STATE_DONE;
        end
        out_enum_val = current_state;
        byte_var = in_data;
        out_typedef_byte = byte_var;
    end
endmodule
class BaseClassEncapsulation;
    local int local_var = 10;
    protected int protected_var = 20;
    local function int get_local_var();
        return local_var;
    endfunction
    protected function int get_protected_var();
        return protected_var;
    endfunction
endclass
class ExtendedClassEncapsulation extends BaseClassEncapsulation;
    function int get_protected_from_extended();
        return protected_var + get_protected_var();
    endfunction
endclass
class NestedClassContainer;
    local int container_local_var = 50;
    class InnerNestedClass;
        function new();
        endfunction
        function int get_container_local_var();
            return container_local_var;
        endfunction
    endclass
endclass
class ClassWithLocalTypedef;
    local typedef logic [15:0] local_word_t;
    local_word_t my_local_word;
    function void set_word(int val);
        my_local_word = val;
    endfunction
endclass
module m_ClassEncapsulation (
    input logic in_trigger,
    output int out_extended_protected_access,
    output int out_nested_local_access,
    output int out_local_violation,
    output int out_protected_violation
);
    BaseClassEncapsulation     base_inst;
    ExtendedClassEncapsulation extended_inst;
    NestedClassContainer     nested_container_inst;
    NestedClassContainer::InnerNestedClass inner_nested_inst;
    ClassWithLocalTypedef     typedef_class_inst;
    always_comb begin
        if (base_inst == null) begin
            base_inst = new();
            extended_inst = new();
            nested_container_inst = new();
            inner_nested_inst = new nested_container_inst.InnerNestedClass();
            typedef_class_inst = new();
        end
        out_extended_protected_access = extended_inst.get_protected_from_extended();
        if (in_trigger) begin
            out_nested_local_access = inner_nested_inst.get_container_local_var();
        end else begin
            out_nested_local_access = 0;
        end
        out_local_violation = base_inst.get_local_var();
        out_protected_violation = base_inst.get_protected_var();
        typedef_class_inst.set_word(123);
    end
endmodule
virtual class AbstractBaseClass;
    pure constraint c_abs;
    int value;
    pure virtual function int get_value();
    pure virtual task set_value(int val);
endclass
class FinalMethodBaseClass;
    function int final_base_method();
        return 100;
    endfunction
    function int initial_base_method();
        return 1;
    endfunction
endclass
class ExtendedMethodClass extends AbstractBaseClass;
    function int get_value();
        return 123;
    endfunction
    task set_value(int val);
        value = val;
    endtask
    function int add_offset(int data, int offset = 5);
        return data + offset;
    endfunction
    function int get_value();
        return super.get_value() + 1;
    endfunction
endclass
class ErrorTriggerClassMethods;
    pure constraint c_err;
    int some_var;
    pure virtual function int pure_virtual_err_func();
    function int warn_initial_method();
        return 10;
    endfunction
    function int err_final_method();
        return 20;
    endfunction
    function int err_extends_no_base();
        return 30;
    endfunction
endclass
class ExtendingErrorTriggerClassMethods extends ErrorTriggerClassMethods;
    function int warn_initial_method();
        return 11;
    endfunction
    function int err_final_method();
        return 21;
    endfunction
endclass
class FinalClassToExtend final;
    int data;
endclass
class IllegalExtenderClass extends FinalClassToExtend;
    function int get_data();
        return data;
    endfunction
endclass
module m_ClassMethodsConstraints (
    input int in_val,
    input int in_offset,
    output int out_method_val,
    output int out_add_offset_val
);
    ExtendedMethodClass test_inst;
    FinalMethodBaseClass final_method_base_inst;
    ErrorTriggerClassMethods error_inst;
    ExtendingErrorTriggerClassMethods extending_error_inst;
    IllegalExtenderClass illegal_extender_inst;
    always_comb begin
        if (test_inst == null) begin
            test_inst = new();
            final_method_base_inst = new();
            error_inst = new();
            extending_error_inst = new();
            illegal_extender_inst = new();
        end
        test_inst.value = in_val;
        out_method_val = test_inst.get_value();
        test_inst.set_value(in_val);
        out_method_val = out_method_val + 1; 
        out_add_offset_val = test_inst.add_offset(in_val);
        if (in_offset != 0) begin
            out_add_offset_val = test_inst.add_offset(in_val, in_offset);
        end
        error_inst.some_var = in_val;
        void'(error_inst.warn_initial_method());
        void'(error_inst.err_final_method());
        void'(error_inst.err_extends_no_base());
        void'(extending_error_inst.warn_initial_method());
        void'(extending_error_inst.err_final_method());
        illegal_extender_inst.data = in_val;
        void'(illegal_extender_inst.get_data());
    end
endmodule
module m_ParamTypeAndRefDType (
    input  int in_width,
    input  logic [31:0] in_data,
    output logic [31:0] out_data_a,
    output logic [31:0] out_data_b,
    output int out_parameterized_class_val
);
    typedef struct packed {
        logic [31:0] data_field;
        logic [1:0]  type_id_field;
    } my_fixed_struct_t;
    my_fixed_struct_t s_fixed;
    class ParameterizedClass #(parameter int SIZE = 8);
        logic [SIZE-1:0] class_data;
        function new();
            class_data = '0;
        endfunction
        function int get_sum();
            int sum = 0;
            for (int i=0; i<SIZE; i++) begin
                sum += class_data[i];
            end
            return sum;
        endfunction
    endclass
    ParameterizedClass #(16) pc16_inst;
    ParameterizedClass #(32) pc32_inst;
    typedef ParameterizedClass #(8) ParamClass8_t;
    typedef ParameterizedClass #(16) ParamClass16_t;
    typedef ParameterizedClass #(32) ParamClass32_t;
    ParamClass8_t pc8_inst_aliased;
    ParamClass16_t pc16_inst_aliased;
    ParamClass32_t pc32_inst_aliased;
    always_comb begin
        if (pc16_inst == null) begin
            pc16_inst = new();
            pc32_inst = new();
            pc8_inst_aliased = new();
            pc16_inst_aliased = new();
            pc32_inst_aliased = new();
        end
        s_fixed.data_field = in_data;
        s_fixed.type_id_field = 2'b01;
        out_data_a = s_fixed.data_field;
        out_data_b = in_data;
        pc16_inst.class_data = in_data[15:0];
        pc32_inst.class_data = in_data;
        pc8_inst_aliased.class_data = in_data[7:0];
        pc16_inst_aliased.class_data = in_data[15:0];
        pc32_inst_aliased.class_data = in_data;
        out_parameterized_class_val = pc16_inst.get_sum() + pc32_inst.get_sum() +
                                      pc8_inst_aliased.get_sum() + pc16_inst_aliased.get_sum() + pc32_inst_aliased.get_sum();
    end
endmodule
