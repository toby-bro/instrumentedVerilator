module ClassFeatureModule (
    input logic clk_i,
    input logic rst_ni,
    output logic [7:0] data_o
);
    typedef enum logic [1:0] {
        STATE_IDLE,
        STATE_RUNNING
    } MyEnumT;
    class BaseClass;
        local int m_local_var;
        protected int m_protected_var;
        int m_public_var;
        local typedef logic [3:0] local_byte_t;
        protected typedef logic [7:0] protected_byte_t;
        typedef logic [15:0] public_word_t;
        local function void local_func();
            $sformat(m_local_var, "Local"); 
        endfunction
        protected task protected_task();
            $sformat(m_protected_var, "Protected"); 
        endtask
        virtual function void public_func();
            $sformat(m_public_var, "Public"); 
        endfunction
        function new();
            m_local_var = 1;
            m_protected_var = 2;
            m_public_var = 3;
        endfunction
    endclass
    class FinalMethodBaseClass;
        function void final_method() : final;
        endfunction: final_method
    endclass
    class DerivedClassExtendsFinalMethod extends FinalMethodBaseClass;
        function void final_method(); 
        endfunction: final_method
    endclass
    class InitialMethodBaseClass;
        function void initial_method() : initial;
        endfunction: initial_method
    endclass
    class DerivedClassExtendsInitialMethod extends InitialMethodBaseClass;
        function void initial_method(); 
        endfunction: initial_method
    endclass
    class ExtendsWithoutBaseMethodClass;
        function void nonexistent_base_method() : extends; 
        endfunction: nonexistent_base_method
    endclass
    class DerivedClass extends BaseClass;
        int m_derived_var;
        function new();
            super.new();
            m_derived_var = 4;
            m_local_var = 10;
            m_protected_var = 20;
            BaseClass::local_byte_t d_local_byte_var = 4'hA;
            BaseClass::protected_byte_t d_protected_byte_var = 8'hAA;
        endfunction
        virtual function void public_func();
            $sformat(m_public_var, "Overridden Public");
            local_func(); 
            protected_task(); 
        endfunction
    endclass
    class OuterClass;
        local int outer_local_member;
        protected int outer_protected_member;
        class InnerClass; 
            function new();
                OuterClass o_inst = new(); 
                o_inst.outer_local_member = 1;
                o_inst.outer_protected_member = 2;
            endfunction
        endclass
        function new();
            outer_local_member = 0;
            outer_protected_member = 0;
        endfunction
    endclass
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            data_o <= 8'h00;
        end else begin
            BaseClass base_inst = new();
            DerivedClass derived_inst = new();
            DerivedClassExtendsFinalMethod final_ext_inst = new();
            DerivedClassExtendsInitialMethod initial_ext_inst = new();
            ExtendsWithoutBaseMethodClass no_base_ext_inst = new();
            OuterClass outer_inst = new();
            OuterClass::InnerClass inner_inst = new();
            base_inst.public_func();
            derived_inst.public_func();
            BaseClass::protected_byte_t pb_var = 8'hAA; 
            BaseClass::local_byte_t lb_var = 4'hA;     
            data_o <= pb_var;
        end
    end
endmodule
module CastAndConstraintModule (
    input logic [31:0] input_data_i,
    output logic [7:0] result_o
);
    class MyIllegalPureConstraintClass; 
        rand int value_x;
        rand int value_y;
        constraint bad_pure_c { pure value_x < value_y; } 
    endclass
    virtual class VirtualClassWithPureConstraint;
        rand int x_val;
        rand int y_val;
        constraint valid_pure_c { pure x_val < y_val; }
    endclass
    interface class InterfaceClassWithPureConstraint;
        rand int z_val;
        constraint iface_pure_c { pure z_val > 0; }
    endclass
    always_comb begin
        int converted_val;
        logic [7:0] byte_val;
        converted_val = int'(input_data_i[15:0]); 
        byte_val = 8'(converted_val); 
        result_o = byte_val + 8'(input_data_i[7:0]); 
    end
endmodule
module TypeDeclarationModule (
    input logic [3:0] input_selection_i,
    output logic [15:0] output_data_o
);
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
    } my_struct_t;
    typedef union packed {
        logic [15:0] full_word;
        my_struct_t parts;
    } my_union_t;
    typedef enum logic [1:0] {
        CMD_READ = 2'b00,
        CMD_WRITE = 2'b01,
        CMD_ERASE = 2'b10,
        CMD_NOP = 2'b11
    } command_e;
    class MyParameterizedClass #(parameter int SIZE = 8);
        logic [SIZE-1:0] data;
        function new(logic [SIZE-1:0] val);
            data = val;
        endfunction
    endclass
    typedef MyParameterizedClass #(16) my_param_class_16_t;
    typedef my_struct_t struct_alias_t;
    typedef command_e cmd_alias_t;
    my_struct_t s_var;
    my_union_t u_var;
    command_e cmd_var;
    my_param_class_16_t param_class_inst;
    struct_alias_t s_alias_var;
    cmd_alias_t cmd_alias_var;
    always_comb begin
        s_var.field_a = 8'h11;
        s_var.field_b = 8'h22;
        u_var.parts = s_var;
        cmd_var = CMD_WRITE;
        s_alias_var = s_var;
        cmd_alias_var = CMD_ERASE;
        if (input_selection_i == 4'h0) begin
            output_data_o = u_var.full_word;
        end else if (input_selection_i == 4'h1) begin
            output_data_o = {14'b0, cmd_var};
        end else begin
            param_class_inst = new(input_selection_i + 'h100);
            output_data_o = param_class_inst.data;
        end
    end
endmodule
module FunctionTaskAndMemberSelModule (
    input logic clk_i,
    input logic [7:0] val_a_i,
    input logic [7:0] val_b_i,
    output logic [15:0] result_o
);
    class InitialMethodBase;
        function void initial_action() : initial;
        endfunction: initial_action
    endclass
    class FinalMethodBase;
        function void final_action() : final;
        endfunction: final_action
    endclass
    virtual class BaseProcessor;
        int base_data;
        pure virtual function int process_data(int input_val);
        virtual function int get_base_data();
            return base_data;
        endfunction
        function int calculate_sum(int a, int b);
            return a + b;
        endfunction
        function new();
            base_data = 100;
        endfunction
    endclass
    class DerivedProcessor extends BaseProcessor;
        int derived_data;
        virtual function int process_data(int input_val);
            return input_val * 2;
        endfunction
        function int get_base_data() : extends;
            return super.get_base_data() + derived_data;
        endfunction
        function new();
            super.new();
            derived_data = 20;
        endfunction
    endclass
    class EncapsulatedMethodsClass;
        local function void local_method();
        endfunction
        protected function void protected_method();
        endfunction
        function void public_method();
            local_method(); 
            protected_method(); 
        endfunction
        function new();
        endfunction
    endclass
    always_ff @(posedge clk_i) begin
        BaseProcessor bp;
        DerivedProcessor dp;
        EncapsulatedMethodsClass emc;
        InitialMethodBase imb = new();
        FinalMethodBase fmb = new();
        dp = new();
        bp = dp; 
        result_o <= bp.process_data(val_a_i) + bp.get_base_data();
        result_o <= result_o + bp.calculate_sum(val_a_i, val_b_i);
        emc = new();
        emc.public_method(); 
        imb.initial_action();
        fmb.final_action();
    end
endmodule
module LifetimeAssignmentModule (
    input logic clk_i,
    input logic rst_ni,
    input logic [7:0] data_in_i,
    output logic [7:0] output_reg_o
);
    logic [7:0] continuous_wire;
    assign continuous_wire = data_in_i; 
    logic [7:0] nonblocking_reg;
    class MyClassWithMembers;
        int non_static_member; 
        int dynamic_array[]; 
        function new();
            non_static_member = 0;
            dynamic_array = new[5]; 
            foreach (dynamic_array[i]) dynamic_array[i] = i;
        endfunction
    endclass
    MyClassWithMembers class_inst; 
    int module_dynamic_array[];
    task automatic example_task_with_args(
        input int in_arg,
        output int out_arg 
    );
        automatic int task_local_auto_var;
        task_local_auto_var = in_arg;
        out_arg = task_local_auto_var;
    endtask
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            nonblocking_reg <= 8'h00;
            output_reg_o <= 8'h00;
            class_inst = new(); 
            module_dynamic_array = new[data_in_i[1:0] + 1]; 
            foreach(module_dynamic_array[idx]) module_dynamic_array[idx] <= 0;
        end else begin
            nonblocking_reg <= data_in_i;
            class_inst.non_static_member <= data_in_i;
            if (!module_dynamic_array.empty()) begin
                module_dynamic_array[0] <= data_in_i;
            end
            if (!class_inst.dynamic_array.empty()) begin
                class_inst.dynamic_array[0] <= data_in_i;
            end
            int temp_out_arg;
            example_task_with_args(data_in_i, temp_out_arg);
            output_reg_o <= nonblocking_reg + continuous_wire + temp_out_arg;
        end
    end
endmodule
module AttributeOfModule (
    input logic [3:0] in_val_i,
    output logic [7:0] out_val_o
);
    function automatic int my_func_with_args_and_return (
        input int arg1,
        input int arg2
    );
        return arg1 + arg2;
    endfunction
    task my_task_with_args (
        input logic [7:0] task_in,
        output logic [7:0] task_out
    );
        task_out = task_in * 2;
    endtask
    always_comb begin
        int f_res;
        logic [7:0] t_out;
        f_res = my_func_with_args_and_return(in_val_i, in_val_i + 1);
        my_task_with_args(in_val_i + 2, t_out);
        out_val_o = f_res + t_out;
    end
endmodule
