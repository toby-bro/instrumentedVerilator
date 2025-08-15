package my_package;
    `timescale 1ns/1ps
    parameter int PKG_CONST = 42;
    int pkg_global_var = 100;
    function int pkg_add(input int p_a, input int p_b);
        return p_a + p_b + PKG_CONST;
    endfunction
endpackage
class MyComplexClass;
    local int m_private_val;
    (* verilator public *) int public_class_val;
    function new(int init_val);
        m_private_val = init_val;
        public_class_val = init_val * 2;
    endfunction
    function int compute_val(int offset);
        return m_private_val + offset;
    endfunction
endclass
class MySimpleClass;
    int m_value;
    function new(int init_val);
        m_value = init_val;
    endfunction
    function int get_value();
        return m_value;
    endfunction
endclass
`timescale 1ns/1ps
module mod_hierarchy_types_params (
    input logic [7:0] data_in,
    input bit         enable,
    output int        result_out,
    output logic [3:0][3:0] matrix_out
);
    (* verilator public *) parameter int   MAX_COUNT = 100;
    (* verilator public *) parameter real  SCALING_FACTOR = 2.5;
    logic [15:0]    internal_reg;
    byte            byte_var;
    bit             flag_bit;
    int             signed_accumulator;
    real            float_value;
    enum {STATE_IDLE, STATE_RUNNING, STATE_DONE, STATE_ERROR} fsm_state;
    logic [7:0] packed_array [4];
    logic       unpacked_array [2][3];
    (* verilator public *) int public_counter;
    always_comb begin : my_combinational_block
        if (enable) begin
            internal_reg = data_in * MAX_COUNT;
            byte_var = data_in;
            float_value = real'(internal_reg) * SCALING_FACTOR;
            flag_bit = (data_in > 50);
            result_out = signed_accumulator;
            matrix_out = '0;
            matrix_out[0][0] = data_in[0];
            public_counter = public_counter + 1;
        end else begin
            internal_reg = '0;
            byte_var = '0;
            float_value = 0.0;
            flag_bit = 0;
            result_out = 0;
            matrix_out = '0;
            public_counter = 0;
        end
        fsm_state = enable ? STATE_RUNNING : STATE_IDLE;
    end
    always_ff @(posedge enable) begin : my_sequential_block
        signed_accumulator <= signed_accumulator + int'(byte_var);
        for (int i=0; i<4; i++) begin
            packed_array[i] <= data_in + i;
        end
        for (int i=0; i<2; i++) begin
            for (int j=0; j<3; j++) begin
                unpacked_array[i][j] <= flag_bit;
            end
        end
    end
    mod_sub_scope u_sub_scope (
        .sub_in(internal_reg[7:0]),
        .sub_out(result_out)
    );
endmodule
module mod_sub_scope (
    input logic [7:0] sub_in,
    output int        sub_out
);
    assign sub_out = sub_in * 2;
endmodule
module mod_dpi_exports (
    input int a,
    input int b,
    output int sum
);
    (* verilator public *) int exported_internal_data = 123;
    (* verilator public *) logic [31:0] writable_exported_data = 32'hFEED_FACE;
    always_comb begin : export_block
        sum = a + b;
    end
    export "DPI-C" function get_exported_data;
    function int get_exported_data();
        return exported_internal_data;
    endfunction
    export "DPI-C" function set_writable_data;
    function void set_writable_data(input logic [31:0] new_val);
        writable_exported_data = new_val;
    endfunction
endmodule
module mod_dpi_imports (
    input byte val_in,
    input real factor,
    input logic [7:0] data_array_in [2],
    input string msg_in,
    output real scaled_val,
    output logic [7:0] processed_array_out [2],
    output string status_msg_out
);
    import "DPI-C" function real C_scale_value(input byte val, input real scale_factor);
    import "DPI-C" function void C_process_array(input logic [7:0] in_arr [2], output logic [7:0] out_arr [2]);
    import "DPI-C" function string C_get_status(input string msg);
    always_comb begin : class_inst_block
        MySimpleClass my_instance;
        my_instance = new(val_in > 0 ? val_in : 0);
        scaled_val = C_scale_value(my_instance.get_value(), factor);
        C_process_array(data_array_in, processed_array_out);
        status_msg_out = C_get_status(msg_in);
    end
endmodule
module mod_coverage (
    input logic [1:0] state_in,
    input bit event_trigger,
    output logic [1:0] next_state
);
    logic [1:0] current_state_reg;
    covergroup StateCoverage;
        coverpoint current_state_reg {
            bins idle = {0};
            bins active = {1};
            bins done = {2};
            bins error = {3};
            illegal_bins illegal_bin = {4};
            ignore_bins ignored_bin = {5};
        }
    endgroup
    StateCoverage cg_inst = new();
    always_ff @(posedge event_trigger) begin : state_update_block
        current_state_reg <= state_in;
        next_state <= state_in;
    end
    covergroup MyOtherCoverage @(posedge event_trigger);
        coverpoint state_in {
            bins low = {0,1};
            bins high = {2,3};
        }
    endgroup
    MyOtherCoverage other_cg_inst = new();
endmodule
module mod_pkg_and_class_consumer (
    input int data_in_class,
    input int data_in_pkg,
    output int class_result,
    output int pkg_result
);
    import my_package::*;
    always_comb begin : class_pkg_usage
        MyComplexClass my_obj;
        my_obj = new(data_in_class > 0 ? data_in_class : 1);
        class_result = my_obj.compute_val(my_obj.public_class_val);
        pkg_result = pkg_add(data_in_pkg, pkg_global_var);
        pkg_global_var = pkg_global_var + 1;
    end
endmodule
module mod_event_handling (
    input bit start_op,
    input bit reset_op,
    output bit operation_done
);
    event start_event;
    event reset_event;
    event complete_event;
    logic is_running_reg;
    logic operation_done_reg;
    always_ff @(posedge start_op or posedge reset_op or complete_event.triggered or reset_event.triggered) begin : main_sequential_logic
        if (reset_op) begin 
            is_running_reg <= 0;
            operation_done_reg <= 0;
            -> reset_event; 
        end else if (start_op) begin 
            is_running_reg <= 1;
            operation_done_reg <= 0; 
            -> start_event; 
        end else if (complete_event.triggered()) begin 
            is_running_reg <= 0; 
            operation_done_reg <= 1;
        end else if (reset_event.triggered()) begin 
            is_running_reg <= 0;
            operation_done_reg <= 0;
        end
    end
    always_comb begin : operation_event_trigger_logic
        if (is_running_reg && !operation_done_reg) begin
            -> complete_event;
        end
    end
    assign operation_done = operation_done_reg; 
endmodule
module mod_savable_params (
    input int config_val,
    output int current_val
);
    parameter int DEFAULT_OFFSET = 5;
    logic [31:0] internal_state_register;
    int          calculated_sum;
    always_comb begin : param_logic
        internal_state_register = config_val + DEFAULT_OFFSET;
        calculated_sum = internal_state_register * 2;
        current_val = calculated_sum;
    end
endmodule
