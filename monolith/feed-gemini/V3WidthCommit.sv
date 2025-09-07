interface TestIf (input logic clk);
    logic data;
    modport master (output data);
    modport slave (input data);
endinterface
module ClassFeatureModule (
    input logic clk,
    input logic reset_n,
    input int input_val,
    output logic output_status,
    output int output_data
);
    TestIf test_if_inst (.*);
    virtual TestIf.master virt_if_master_port;
    virtual class BaseClass;
        local int m_local_var = 10;
        protected int m_protected_var = 20;
        int m_public_var = 30;
        function new();
        endfunction
        pure virtual function int get_value();
        pure virtual task do_something(input int val);
        function automatic int get_local();
            return m_local_var;
        endfunction
        function int get_protected();
            return m_protected_var;
        endfunction
        virtual function int get_public_final() final;
            return m_public_var;
        endfunction
        virtual function int initial_method();
            return m_public_var + 1;
        endfunction
        pure constraint c_pure {
            m_public_var > 0;
        };
    endclass
    class DerivedClass extends BaseClass;
        int m_derived_var = 100;
        function new();
            super.new();
        endfunction
        function int get_value();
            return m_derived_var + m_public_var;
        endfunction
        task do_something(input int val);
            m_derived_var = val;
        endtask
        function int extends_method() extends;
            return super.initial_method() + 5;
        endfunction
        function int access_encapsulated();
            int val;
            val = m_protected_var;
            return val;
        endfunction
        function int access_base_method_encapsulated();
            int val;
            val = super.get_protected();
            return val;
        endfunction
    endclass
    class AnotherDerivedClass extends DerivedClass;
        function new();
            super.new();
        endfunction
    endclass
    BaseClass inst_derived;
    AnotherDerivedClass inst_another_derived;
    always_ff @(posedge clk or negedge reset_n) begin
        automatic DerivedClass temp_derived;
        if (!reset_n) begin
            output_status <= 1'b0;
            output_data <= 0;
            if (inst_derived == null) begin
                inst_derived = DerivedClass::new();
            end
            if (inst_another_derived == null) begin
                inst_another_derived = AnotherDerivedClass::new();
            end
            if (test_if_inst.master != null) begin
                virt_if_master_port = test_if_inst.master;
            end
        end else begin
            if (inst_derived != null) begin
                output_data <= inst_derived.get_value() + input_val;
                inst_derived.do_something(input_val);
                if ($cast(temp_derived, inst_derived)) begin
                    output_status <= (temp_derived.access_encapsulated() != 0) ? 1'b1 : 1'b0;
                    output_status <= (temp_derived.access_base_method_encapsulated() != 0) ? 1'b1 : 1'b0;
                    output_data <= temp_derived.extends_method();
                    temp_derived.m_derived_var <= input_val + output_data;
                end
            end
            if (inst_another_derived != null) begin
                output_data <= inst_another_derived.get_public_final();
            end
            if (virt_if_master_port != null) begin
                virt_if_master_port.data <= input_val[0];
            end
        end
    end
endmodule
module AssignmentAndDataTypeModule (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output int out_diff,
    output logic out_flag,
    output int out_comb_sum,
    output int out_dynamic_array_size
);
    logic [15:0] intermediate_val;
    assign intermediate_val = in_a + in_b + 16'hABCD;
    reg [7:0] reg_a, reg_b;
    always_ff @(posedge intermediate_val[0]) begin
        reg_a <= in_a;
        reg_b <= in_b;
    end
    typedef enum logic [1:0] {
        STATE_IDLE = 2'b00,
        STATE_BUSY = 2'b01,
        STATE_DONE = 2'b10
    } my_state_e;
    my_state_e current_state;
    typedef struct packed {
        logic [3:0] field1;
        logic [3:0] field2;
    } my_struct_t;
    my_struct_t s_var;
    typedef union packed {
        logic [7:0] byte_val;
        logic [1:0][3:0] nibbles;
    } my_union_t;
    my_union_t u_var;
    int cast_result;
    always_comb begin
        current_state = my_state_e'(intermediate_val[1:0]);
        s_var.field1 = intermediate_val[7:4];
        s_var.field2 = intermediate_val[3:0];
        u_var.byte_val = intermediate_val[7:0];
        out_comb_sum = current_state + 12345;
        out_diff = int'(in_a) - 50;
        out_flag = (current_state == STATE_DONE);
    end
    int my_dynamic_array[];
    always_ff @(posedge intermediate_val[0]) begin
        if (reg_a > reg_b) begin
            my_dynamic_array = new[reg_a - reg_b];
        end else begin
            my_dynamic_array = new[1];
        end
        out_dynamic_array_size <= my_dynamic_array.size();
    end
endmodule
module FunctionAttributeAndParamTypeModule (
    input int func_in,
    input logic [7:0] param_type_in,
    output int func_out,
    output logic [7:0] param_type_out
);
    function automatic int my_complex_function(
        input int arg1,
        input logic [15:0] arg2
    );
        return arg1 + arg2;
    endfunction
    task my_simple_task(output int result);
        result = 5;
    endtask
    parameter type MY_INT_TYPE = int;
    MY_INT_TYPE internal_int_var;
    int task_out_var;
    parameter type MY_STRUCT_TYPE = struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
    };
    MY_STRUCT_TYPE internal_struct_var;
    always_comb begin
        func_out = my_complex_function(func_in, 16'h1234);
        my_simple_task(task_out_var);
        param_type_out = internal_struct_var.field_a + param_type_in;
    end
    always_ff @(func_in) begin
        internal_int_var <= func_in + 1 + task_out_var;
        internal_struct_var.field_a <= param_type_in;
        internal_struct_var.field_b <= param_type_in + 1;
    end
endmodule
module BasicTypeAndArrayModule (
    input byte data_in,
    input int idx_in,
    output int data_out,
    output int array_sum
);
    logic [31:0] reg_32bit_val;
    bit signed [7:0] signed_byte;
    int unsigned unsigned_int_val;
    logic [7:0] my_static_array [0:15];
    logic [7:0] my_unpacked_array [16];
    int constant_val = 10;
    int hex_val = 'hFF;
    int bin_val = 8'b11110000;
    always_ff @(posedge data_in[0]) begin
        reg_32bit_val <= data_in + constant_val;
        signed_byte <= $signed(data_in);
        unsigned_int_val <= $unsigned(hex_val);
        my_static_array[idx_in[3:0]] <= data_in;
        my_unpacked_array[idx_in[3:0]] <= data_in + 1;
    end
    int sum_local;
    always_comb begin
        sum_local = 0;
        for (int i=0; i<16; i++) begin
            sum_local = sum_local + my_static_array[i] + my_unpacked_array[i];
        end
        array_sum = sum_local;
        data_out = signed_byte + unsigned_int_val + bin_val;
    end
endmodule
