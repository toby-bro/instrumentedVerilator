module ModuleFeatures_BasicHierarchy (
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    logic [7:0] local_var;
    logic [7:0] another_var;
    begin : named_block
        logic [7:0] block_var; 
        assign block_var = in_data;
        begin
            logic [7:0] unnamed_block_var; 
            assign unnamed_block_var = block_var;
            local_var = unnamed_block_var;
        end
        begin
            logic [7:0] another_unnamed_block_var; 
            assign another_unnamed_block_var = local_var;
            out_data = another_unnamed_block_var;
        end
        logic [7:0] local_var; 
        assign local_var = 8'd10; 
    end
    logic [7:0] another_var; 
    assign another_var = 8'd20;
endmodule
module ModuleFeatures_Parameters #(
    parameter int P_VAL = 10, 
    localparam int LP_VAL = P_VAL + 5, 
    parameter type P_TYPE = logic [3:0] 
) (
    input P_TYPE in_param_data,
    output P_TYPE out_param_data
);
    P_TYPE internal_param_var; 
    assign internal_param_var = in_param_data + LP_VAL;
    assign out_param_data = internal_param_var;
    logic [P_VAL-1:0] sized_vec; 
    assign sized_vec = P_VAL; 
    P_TYPE typed_var;
    assign typed_var = in_param_data;
endmodule
interface my_interface (
    input bit clk
);
    logic [3:0] data; 
    modport master ( 
        input clk,
        output data,
        export function get_data 
    );
    modport slave ( 
        input clk,
        input data
    );
    function int get_data(); 
        return data;
    endfunction
    pure virtual function void pure_func_in_iface(); 
    pure virtual constraint my_iface_constraint; 
    class IfaceClass; 
        int iface_class_var;
        pure virtual function void pure_method_in_iface_class();
    endclass
endinterface
module ModuleFeatures_Interfaces (
    input bit clk_in,
    output logic [3:0] out_val
);
    my_interface iface_instance ( 
        .clk (clk_in)
    );
    my_interface iface_var_local; 
    assign iface_var_local.data = 4'hA; 
    logic [3:0] internal_data_m;
    assign iface_instance.master.data = internal_data_m; 
    assign out_val = iface_instance.master.get_data();
    virtual my_interface virtual_iface_var;
endmodule
module ModuleFeatures_Classes (
    input bit clk_in,
    input int class_in,
    output int class_out
);
    class MyBaseClass; 
        int base_var;
        function new(); 
            base_var = 10;
        endfunction
        function int get_base_var(); 
            return base_var;
        endfunction
        pure virtual function int get_data_pure(); 
        pure virtual constraint base_constraint; 
        localparam int LOCAL_CLASS_PARAM = 20; 
    endclass
    class MyDerivedClass extends MyBaseClass; 
        int derived_var;
        function new(); 
            super.new(); 
        endfunction
        function int get_derived_var();
            return derived_var + super.get_base_var(); 
        endfunction
        function int get_data_pure(); 
            return derived_var;
        endfunction
        constraint derived_constraint { derived_var > 0; } 
        function int get_this_var();
            return this.derived_var; 
        endfunction
    endclass
    MyDerivedClass my_obj;
    always_comb begin
        if (clk_in) begin 
            my_obj = new(); 
            class_out = my_obj.get_derived_var() + my_obj.get_data_pure() + MyBaseClass::LOCAL_CLASS_PARAM; 
        end
    end
    class ParameterizedClass #(parameter int PARAM_C = 10);
        int val = PARAM_C;
        function int get_val(); return val; endfunction
    endclass
    class ExtendsParamClass extends ParameterizedClass #(20);
        int ext_val;
        function new();
            super.new(); 
            ext_val = 1;
        endfunction
    endclass
    ExtendsParamClass ext_param_obj; 
    always_comb begin
        if (clk_in) begin
            ext_param_obj = new();
            class_out = class_out + ext_param_obj.get_val(); 
        end
    end
    interface class IFaceProto; 
        pure virtual function void method();
    endclass
    class AnonExtend implements IFaceProto; 
        function void method();
        endfunction
    endclass
endmodule
module ModuleFeatures_ClassMethods (
    input bit clk,
    input int rand_seed,
    output int rand_val
);
    class RandClass;
        rand int x;
        rand int y;
        constraint c1 { x > 0; x < 100; }
        constraint c2 { y > 0; y < 100; }
        constraint c3 { x + y < 150; }
        pure virtual constraint my_pure_constraint; 
        constraint my_pure_constraint_impl { x != y; } 
        pure virtual function int get_rand_val();
        function int get_rand_val(); 
            return x + y;
        endfunction
    endclass
    RandClass rand_obj;
    always_comb begin
        rand_val = 0; 
        if (clk) begin
            rand_obj = new();
            void'(rand_obj.randomize());
            void'(rand_obj.randomize() with {
                x inside { [10:20] };
                y == local::x * 2; 
                my_pure_constraint_impl.constraint_mode(0); 
            });
            rand_obj.srandom(rand_seed); 
            rand_obj.get_randstate(); 
            rand_obj.set_randstate(null); 
            rand_val = rand_obj.get_rand_val();
        end
    end
endmodule
package my_package;
    int package_var = 100;
    function int get_package_var();
        return package_var;
    endfunction
    typedef logic [15:0] pkg_wide_bus; 
endpackage
package another_package;
    import my_package::*; 
    int another_pkg_var = 200;
    export my_package::get_package_var; 
endpackage
module ModuleFeatures_Packages (
    input logic [7:0] in_pkg_data,
    output logic [7:0] out_pkg_data
);
    import my_package::package_var; 
    import another_package::another_pkg_var; 
    always_comb begin
        out_pkg_data = package_var + another_pkg_var + my_package::get_package_var(); 
    end
    pkg_wide_bus my_bus_from_pkg; 
    assign my_bus_from_pkg = in_pkg_data;
endmodule
module top_level_module (
    input int top_in,
    output int top_out
);
    int top_level_var = 1;
    sub_module_a inst_a (
        .sub_in (top_in),
        .sub_out (top_out)
    );
    sub_module_b inst_b (
        .b_in (top_in),
        .b_out (top_out)
    );
    assign top_level_var = inst_a.named_block_in_sub.block_local_var; 
    ParameterizedModule #(.PARAM(10)) param_inst_1 (); 
    assign top_out = param_inst_1.PARAM; 
    generate
        if (1) begin : gen_if_block 
            logic [7:0] gen_local_var;
            assign gen_local_var = top_in;
            assign top_out = gen_if_block.gen_local_var; 
        end
    endgenerate
    clocking my_top_cb @(posedge top_in); 
        input clk_in_cb; 
    endclocking
    logic event_fired;
    always @(my_top_cb) begin : event_block 
        event_fired = 1;
    end
endmodule
module sub_module_a (
    input int sub_in,
    output int sub_out
);
    int sub_local_var = 2;
    begin : named_block_in_sub
        int block_local_var = sub_in + sub_local_var;
    end
endmodule
module sub_module_b (
    input int b_in,
    output int b_out
);
    int b_local_var = 3;
    assign b_out = b_in + b_local_var;
endmodule
module ParameterizedModule #(parameter int PARAM = 5) (
);
endmodule
module ModuleFeatures_Types (
    input bit [3:0] in_raw,
    output logic [7:0] out_struct_val
);
    typedef logic [15:0] my_word_t;
    my_word_t word_var;
    assign word_var = {12'b0, in_raw};
    typedef enum {STATE_IDLE, STATE_RUNNING, STATE_DONE} my_state_e;
    my_state_e current_state;
    assign current_state = STATE_IDLE; 
    typedef struct packed {
        logic [3:0] field_a;
        logic [3:0] field_b;
    } my_struct_t;
    my_struct_t my_struct_var;
    assign my_struct_var.field_a = in_raw;
    assign my_struct_var.field_b = 4'hF;
    assign out_struct_val = {my_struct_var.field_a, my_struct_var.field_b};
    typedef union packed {
        logic [7:0] as_byte;
        my_struct_t as_struct;
    } my_union_t;
    my_union_t my_union_var;
    assign my_union_var.as_struct = my_struct_var;
    assign out_struct_val = my_union_var.as_byte; 
    parameter type GLOBAL_MY_PARAM_TYPE = int;
    GLOBAL_MY_PARAM_TYPE my_param_type_var;
    assign my_param_type_var = 123;
    function automatic typeof(my_param_type_var) get_typeof_var();
        return my_param_type_var;
    endfunction
    assign out_struct_val = out_struct_val + get_typeof_var();
    typedef class MyFwdClass; 
    MyFwdClass fwd_obj; 
    class MyFwdClass; int dummy_val; endclass 
    logic [7:0] packed_array [0:1]; 
    assign packed_array = {8'h11, 8'h22}; 
endmodule
module ModuleFeatures_AdvancedBlocks (
    input logic clk,
    input logic rst_n,
    input int [3:0] data_array [0:2], 
    output int out_sum_array,
    output logic disable_status
);
    int sum = 0;
    always_comb begin
        sum = 0;
        foreach (data_array[i]) begin 
            sum = sum + data_array[i];
        end
        out_sum_array = sum;
    end
    task my_task(); 
        logic task_var;
        begin : inner_block 
            assign task_var = 1'b1;
            disable inner_block; 
        end
        disable my_task; 
    endtask
    always_comb begin
        if (rst_n) begin
            my_task(); 
            disable_status = 1;
        end else begin
            disable_status = 0;
        end
    end
endmodule
module ModuleFeatures_ImplicitAndPorts (
    input logic [7:0] ansi_in,       
    output logic [7:0] ansi_out,     
    inout logic [7:0] ansi_inout_var 
);
    input [7:0] traditional_input_port;
    output [7:0] traditional_output_port;
    inout [7:0] traditional_inout_port;
    assign implicit_wire_a = ansi_in; 
    assign implicit_wire_b = traditional_input_port;
    assign ansi_out = implicit_wire_a; 
    assign implicit_assign_w = 8'd123;
    wire [7:0] explicit_wire;
    assign explicit_wire = implicit_assign_w;
    pullup(implicit_pulled_up_wire);
    input traditional_input_port; 
    logic [7:0] hidden_var;
    begin : hiding_block
        logic [7:0] hidden_var; 
        assign hidden_var = 8'd7;
    end
    assign traditional_output_port = implicit_wire_b;
    assign traditional_inout_port = ansi_inout_var;
endmodule
