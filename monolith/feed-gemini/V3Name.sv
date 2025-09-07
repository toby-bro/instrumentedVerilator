module sv_hierarchy_child (
    input logic child_in_data,
    output logic child_out_data
);
    logic [7:0] internal_reg_var;
    logic       internal_wire_var;
    assign internal_wire_var = child_in_data;
    logic module_logic_variable;
    always_comb begin
        internal_reg_var = internal_reg_var + 1;
        module_logic_variable = internal_wire_var;
        child_out_data = internal_reg_var[0];
    end
endmodule
module sv_simple_naming_module (
    input logic i_a,
    output logic o_b
);
    logic [3:0] local_reg_sig;
    logic       local_wire_sig;
    int         local_int_sig;
    logic logic_keyword_var;
    logic reg_keyword_var;
    parameter parameter_val = 10;
    always_comb begin
        local_reg_sig  = i_a ? 4'd1 : 4'd0;
        local_wire_sig = local_reg_sig[0];
        local_int_sig  = parameter_val + 1;
        logic_keyword_var = local_wire_sig;
        reg_keyword_var   = logic_keyword_var;
        o_b = reg_keyword_var;
    end
endmodule
module sv_structured_types_module (
    input logic [7:0] i_data_in,
    output logic [15:0] o_packed_data_out
);
    typedef struct packed {
        logic [7:0] field_struct_a;
        logic       field_struct_b;
        int         field_struct_c;
    } my_packed_struct_t;
    typedef union packed {
        logic [15:0] union_data16;
        logic [1:0][7:0]  union_data8;
    } my_packed_union_t;
    my_packed_struct_t struct_instance;
    my_packed_union_t  union_instance;
    always_comb begin
        struct_instance.field_struct_a = i_data_in;
        struct_instance.field_struct_b = i_data_in[0];
        struct_instance.field_struct_c = 42;
        union_instance.union_data16 = {struct_instance.field_struct_a, {1'b0, struct_instance.field_struct_b, 6'b0}};
        o_packed_data_out = union_instance.union_data16;
    end
endmodule
module sv_dpi_and_procedural_class (
    input int i_value_in,
    input logic i_clk,
    output int o_result_out
);
    import "DPI-C" function int dpi_add_values(int a, int b);
    import "DPI-C" function void dpi_set_output(int val);
    import "DPI-C" function void dpi_delete_handle(int handle);
    function void sv_exported_function(int val);
    endfunction
    export "DPI-C" function sv_exported_function;
    class MySvClass;
        int class_internal_data;
        function new(int init_val);
            class_internal_data = init_val;
        endfunction
        function int get_class_data();
            return class_internal_data;
        endfunction
    endclass
    MySvClass class_handle;
    int dpi_func_result;
    always_ff @(posedge i_clk) begin
        if (i_value_in > 0) begin
            dpi_func_result = dpi_add_values(i_value_in, 7);
            dpi_set_output(dpi_func_result);
            class_handle = new(dpi_func_result);
            o_result_out <= class_handle.get_class_data();
            sv_exported_function(dpi_func_result);
        end else begin
            dpi_func_result = 0;
            o_result_out <= 0;
            if (class_handle != null) begin
                dpi_delete_handle(class_handle.class_internal_data);
            end
        end
    end
endmodule
module sv_hierarchy_parent (
    input logic parent_in_control,
    output logic parent_out_status
);
    logic child_instance_output;
    sv_hierarchy_child child_instance (
        .child_in_data (parent_in_control),
        .child_out_data(child_instance_output)
    );
    logic accessed_child_internal_var;
    assign accessed_child_internal_var = child_instance.internal_reg_var[0];
    always_comb begin
        parent_out_status = child_instance_output & accessed_child_internal_var;
    end
endmodule
package sv_types_package;
    typedef enum {
        STATE_IDLE_PKGS,
        STATE_ACTIVE_PKGS,
        STATE_PAUSED_PKGS,
        STATE_DONE_PKGS
    } my_package_enum_t;
    function automatic int get_enum_numeric_value(my_package_enum_t state);
        return int'(state);
    endfunction
endpackage
module sv_package_and_enum_array (
    input bit [1:0] i_selection,
    output int o_derived_status_code
);
    import sv_types_package::*;
    my_package_enum_t current_state_from_pkg;
    my_package_enum_t state_history_array [4];
    always_comb begin
        case (i_selection)
            2'b00: current_state_from_pkg = STATE_IDLE_PKGS;
            2'b01: current_state_from_pkg = STATE_ACTIVE_PKGS;
            2'b10: current_state_from_pkg = STATE_PAUSED_PKGS;
            default: current_state_from_pkg = STATE_DONE_PKGS;
        endcase
        state_history_array[0] = STATE_IDLE_PKGS;
        state_history_array[1] = STATE_ACTIVE_PKGS;
        state_history_array[2] = current_state_from_pkg;
        state_history_array[3] = STATE_DONE_PKGS;
        o_derived_status_code = get_enum_numeric_value(current_state_from_pkg);
    end
endmodule
