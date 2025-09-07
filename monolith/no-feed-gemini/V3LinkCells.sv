module SimpleModule (
    input logic in_data,
    output logic out_data
);
    assign out_data = in_data;
endmodule
module TopModuleInstantiateSimple (
    input logic in_val,
    output logic out_val
);
    logic mid_sig;
    SimpleModule inst_simple (.in_data(in_val), .out_data(mid_sig));
    assign out_val = mid_sig;
endmodule
module ModuleA (
    input int recursion_counter,
    output int val_out_A
);
    int temp_val_B;
    if (recursion_counter > 0) begin : gen_recurse_A
        ModuleB inst_b (
            .recursion_counter(recursion_counter - 1),
            .val_out_B(temp_val_B)
        );
        assign val_out_A = temp_val_B + 1;
    end else begin
        assign val_out_A = 1;
    end
endmodule
module ModuleB (
    input int recursion_counter,
    output int val_out_B
);
    int temp_val_C;
    if (recursion_counter > 0) begin : gen_recurse_B
        ModuleC inst_c (
            .recursion_counter(recursion_counter - 1),
            .val_out_C(temp_val_C)
        );
        assign val_out_B = temp_val_C + 1;
    end else begin
        assign val_out_B = 1;
    end
endmodule
module ModuleC (
    input int recursion_counter,
    output int val_out_C
);
    int temp_val_A;
    if (recursion_counter > 0) begin : gen_recurse_C
        ModuleA inst_a (
            .recursion_counter(recursion_counter - 1),
            .val_out_A(temp_val_A)
        );
        assign val_out_C = temp_val_A + 1;
    end else begin
        assign val_out_C = 1;
    end
endmodule
module TopModuleIndirectRecursive (
    input int start_depth,
    output int final_result
);
    ModuleA start_inst (.recursion_counter(start_depth), .val_out_A(final_result));
endmodule
interface MyInterface (input logic clk);
    logic data_in;
    logic data_out;
    modport master (input data_in, output data_out, input clk);
    modport slave (output data_in, input data_out, input clk);
endinterface
module ModuleUsingIface (
    input logic sys_clk,
    output logic interface_test_out
);
    MyInterface iface_inst (.clk(sys_clk));
    assign iface_inst.data_in = 1'b1;
    assign interface_test_out = iface_inst.data_out;
    MyInterface iface_var;
endmodule
class MyBaseClass;
    int base_val;
    function new();
        base_val = 10;
    endfunction
endclass
class ClassUsingVirtualIface extends MyBaseClass;
    virtual MyInterface v_iface;
    int class_output;
    function new(virtual MyInterface iface_h);
        super.new();
        v_iface = iface_h;
        class_output = 0;
    endfunction
    final begin
        if (v_iface != null) begin
            v_iface.data_in = base_val[0];
            class_output = v_iface.data_out;
        end
    end
endclass
module TopModuleIface (
    input logic clk_in,
    output logic iface_result_out
);
    ModuleUsingIface main_iface_mod (.sys_clk(clk_in), .interface_test_out(iface_result_out));
    MyInterface virt_if_inst (.clk(clk_in));
    ClassUsingVirtualIface my_class_inst;
    final begin
        my_class_inst = new(virt_if_inst);
    end
endmodule
package SourcePackage;
    parameter int SOURCE_PARAM = 100;
endpackage
package IntermediatePackage;
    export SourcePackage::*;
endpackage
module ModuleAccessingExportedPackage (
    input bit enable_access,
    output int exported_val
);
    import IntermediatePackage::*;
    assign exported_val = enable_access ? SOURCE_PARAM : 0;
endmodule
module TopModuleExportPackage (
    input bit top_enable,
    output int top_exported_val
);
    ModuleAccessingExportedPackage exporter_access_inst (.enable_access(top_enable), .exported_val(top_exported_val));
endmodule
module TargetModule (
    input logic target_in,
    output logic target_out
);
    logic internal_signal;
    assign internal_signal = target_in;
    assign target_out = internal_signal;
endmodule
module MonitorModule (
    input logic monitored_sig,
    output logic monitor_status
);
    assign monitor_status = monitored_sig;
endmodule
module TopModuleBind (
    input logic main_input,
    output logic main_output
);
    TargetModule my_target_inst (.target_in(main_input), .target_out(main_output));
    bind my_target_inst : MonitorModule monitor_inst (
        .monitored_sig(my_target_inst.internal_signal),
        .monitor_status()
    );
endmodule
class BaseClass #(parameter int BASE_OFFSET = 5);
    int base_data;
    function new();
        base_data = BASE_OFFSET + 1;
    endfunction
endclass
class DerivedClass #(localparam int DERIVED_FACTOR = 2) extends BaseClass #(DERIVED_FACTOR + 3);
    int derived_data;
    function new();
        super.new();
        derived_data = base_data * DERIVED_FACTOR;
    endfunction
endclass
module TopModuleClasses (
    input logic enable_class_ops,
    output int class_result
);
    DerivedClass my_derived_obj;
    final begin
        my_derived_obj = new();
        if (my_derived_obj != null) begin
            class_result = my_derived_obj.derived_data;
        end else begin
            class_result = 0;
        end
    end
endmodule
module ModuleWithManyPorts (
    input logic in_a,
    input logic in_b = 1'b0,
    output logic out_c,
    output logic out_d,
    input logic in_e
);
    assign out_c = in_a ^ in_b;
    assign out_d = in_e;
endmodule
module InstanceTester (
    input logic test_in1,
    input logic test_in2,
    output logic test_out1,
    output logic test_out2
);
    logic wire_c;
    logic wire_d;
    ModuleWithManyPorts inst1 (test_in1, test_in2, wire_c, wire_d, 1'b1);
    assign test_out1 = wire_c;
    logic inst2_in_a;
    logic inst2_in_b;
    logic inst2_out_c;
    logic inst2_out_d;
    logic inst2_in_e;
    assign inst2_in_a = test_in1;
    assign inst2_in_b = test_in2;
    assign inst2_in_e = 1'b0;
    ModuleWithManyPorts inst2 (.*);
    assign test_out2 = inst2_out_c;
    ModuleWithManyPorts inst4_missing (
        .out_c(),
        .out_d()
    );
endmodule
module TopModuleInstanceTester (
    input logic system_input_a,
    input logic system_input_b,
    output logic system_output_x,
    output logic system_output_y
);
    InstanceTester tester_inst (
        .test_in1(system_input_a),
        .test_in2(system_input_b),
        .test_out1(system_output_x),
        .test_out2(system_output_y)
    );
endmodule
module TypedefModule (
    input logic [7:0] data_in_bus,
    output logic [15:0] result_out_bus
);
    typedef struct packed {
        logic [3:0] field1;
        logic [3:0] field2;
    } my_struct_t;
    typedef enum logic [1:0] {
        STATE_IDLE = 2'b00,
        STATE_BUSY = 2'b01,
        STATE_DONE = 2'b10
    } my_enum_t;
    typedef union packed {
        logic [7:0] byte_val;
        logic [3:0] nibble_vals [2];
    } my_union_t;
    my_struct_t s_var;
    my_enum_t e_state = STATE_IDLE;
    my_union_t u_var;
    logic [7:0] byte_data;
    int integer_data;
    assign s_var.field1 = data_in_bus[7:4];
    assign s_var.field2 = data_in_bus[3:0];
    assign byte_data = s_var.field1 + s_var.field2;
    always_comb begin
        case (e_state)
            STATE_IDLE: integer_data = 1;
            STATE_BUSY: integer_data = 2;
            STATE_DONE: integer_data = 3;
            default: integer_data = 0;
        endcase
    end
    final begin
        u_var.byte_val = byte_data;
        result_out_bus = {u_var.nibble_vals[0], u_var.nibble_vals[1], integer_data[3:0], s_var.field1};
    end
endmodule
module TopModuleTypedef (
    input logic [7:0] input_data_top,
    output logic [15:0] output_result_top
);
    TypedefModule typedef_inst (
        .data_in_bus(input_data_top),
        .result_out_bus(output_result_top)
    );
endmodule
config my_config_1;
    design top_module_config;
endconfig
config my_config_2;
    design TopModuleConfig;
    rule TopModuleConfig use SimpleModule;
    cell TopModuleConfig.inst_simple : SimpleModule;
    use my_config_1;
endconfig
module TopModuleConfig (
    input logic cfg_in,
    output logic cfg_out
);
    assign cfg_out = cfg_in;
endmodule
