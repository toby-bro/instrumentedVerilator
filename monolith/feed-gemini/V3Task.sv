module SimpleInliningAndWireAssign (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    wire [7:0] temp_wire_assign;
    logic [7:0] local_var_in_module;
    function automatic logic [7:0] add_one(input logic [7:0] val);
        logic [7:0] internal_func_var;
        internal_func_var = val + 1;
        return internal_func_var;
    endfunction
    task automatic set_local_var(input logic [7:0] val);
        local_var_in_module = val;
    endtask
    assign temp_wire_assign = in_val;
    always_comb begin
        out_val = add_one(temp_wire_assign);
        set_local_var(out_val);
    end
endmodule
module NoInlinePragmaAndImpure (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic [7:0] out_sum
);
    logic [7:0] module_global_impure_var;
    (* verilator_no_inline_task *)
    task automatic add_and_store_impure(input logic [7:0] val);
        module_global_impure_var = val + in_b;
    endtask
    always_comb begin
        add_and_store_impure(in_a);
        out_sum = module_global_impure_var;
    end
endmodule
module FuncArgVariations (
    input logic         in_arg_bool,
    input int           in_arg_scalar,
    input logic [63:0]  in_arg_wide,
    output int          out_result_a,
    output int          out_result_b,
    output int          out_result_c,
    output logic [63:0] wide_func_result
);
    int io_var;
    int ref_var;
    int const_ref_var;
    task automatic my_complex_task (
        input logic         i_bool,
        input int           i_scalar,
        input int           i_default_val,
        output int          o_out,
        inout int           io_inout_val,
        ref int             r_ref_val,
        const ref int       cr_const_ref_val
    );
        o_out = i_scalar + (i_bool ? 1 : 0) + i_default_val;
        io_inout_val = io_inout_val * 2;
        r_ref_val = r_ref_val + 5;
    endtask
    function automatic logic [63:0] process_wide_val(input logic [63:0] wide_in);
        return wide_in + 1;
    endfunction
    always_comb begin
        io_var = 10;
        ref_var = 20;
        const_ref_var = 30;
        my_complex_task(in_arg_bool, in_arg_scalar, 555, out_result_a, io_var, ref_var, const_ref_var);
        my_complex_task(.i_scalar(in_arg_scalar + 1), .r_ref_val(ref_var),
                        .o_out(out_result_b), .i_bool(in_arg_bool),
                        .io_inout_val(io_var), .cr_const_ref_val(const_ref_var),
                        .i_default_val(666));
        my_complex_task(in_arg_bool, in_arg_scalar, 777, out_result_c, io_var, ref_var, const_ref_var);
        wide_func_result = process_wide_val(in_arg_wide);
    end
endmodule
module ClassAndConstructorInit (
    input logic trigger_read,
    output logic [7:0] class_data_out
);
    class MyClass;
        logic [7:0] m_data;
        logic [7:0] m_init_auto_val;
        function new();
            m_data = 8'hAA;
            m_data = m_data + 1;
            m_init_auto_val = 8'h12;
        endfunction
        function void read_data(output logic [7:0] data);
            data = m_data + m_init_auto_val;
        endfunction
    endclass
    MyClass my_instance;
    logic class_instantiated_reg = 1'b0;
    always_comb begin
        if (!class_instantiated_reg) begin
            my_instance = new();
            class_instantiated_reg = 1'b1;
        end
        if (trigger_read && class_instantiated_reg) begin
            my_instance.read_data(class_data_out);
        end else begin
            class_data_out = 8'h00;
        end
    end
endmodule
module DPI_Import_Export_Types (
    input int             in_int_val,
    input logic [63:0]    in_wide_logic,
    input byte            in_byte_arr [2],
    output int            out_ret_val,
    output string         out_string_from_dpi,
    output longint        out_handle_from_dpi,
    output logic          out_non_local_flag_readback
);
    logic non_local_flag_written_by_dpi = 1'b0;
    chandle my_chandle_var;
    logic [7:0] my_unpacked_bytes[2];
    import "DPI-C" context function int my_dpi_import_func(
        input int a,
        output string s,
        inout chandle h
    );
    import "DPI-C" function void my_dpi_import_task(
        input logic [63:0]    lw,
        inout logic [7:0]     unpacked_bytes[],
        input bit [3:0]       packed_bits
    );
    import "DPI-C" function longint convert_chandle_to_longint(input chandle h);
    function int my_dpi_export_func(input int val, output bit [31:0] bvec);
        bvec = val * 2;
        non_local_flag_written_by_dpi = ~non_local_flag_written_by_dpi;
        return val + 100;
    endfunction
    task my_dpi_export_task(input string name);
    endtask
    export "DPI-C" function my_dpi_export_func;
    export "DPI-C" task my_dpi_export_task;
    always_comb begin
        int dummy_exp_bvec;
        int dummy_exp_ret;
        my_chandle_var = null;
        my_unpacked_bytes[0] = in_byte_arr[0];
        my_unpacked_bytes[1] = in_byte_arr[1];
        out_ret_val = my_dpi_import_func(in_int_val, out_string_from_dpi, my_chandle_var);
        out_handle_from_dpi = convert_chandle_to_longint(my_chandle_var);
        my_dpi_import_task(in_wide_logic, my_unpacked_bytes, 4'b1010);
        dummy_exp_ret = my_dpi_export_func(in_int_val, dummy_exp_bvec);
        my_dpi_export_task("Test String");
        out_non_local_flag_readback = non_local_flag_written_by_dpi;
    end
endmodule
module ControlFlowSpecifics (
    input int     counter_in,
    input logic   cond_in,
    input logic   event_trigger,
    output int    while_sum_out,
    output int    with_result,
    output logic  func_in_sen_list_trigger
);
    int while_sum;
    logic func_in_sen_list_trigger_reg = 1'b0;
    function automatic int calculate_with_return(input int val);
        return val * 2;
    endfunction
    task automatic loop_task(input int limit);
        int i = 0;
        while_sum = 0;
        while (i < limit) begin
            while_sum = while_sum + i;
            i++;
        end
    endtask
    function automatic int get_event_val(input logic trigger);
        return trigger ? 1 : 0;
    endfunction
    always_comb begin
        with_result = calculate_with_return(counter_in);
        loop_task(counter_in);
        while_sum_out = while_sum;
        func_in_sen_list_trigger = func_in_sen_list_trigger_reg;
    end
    always @(get_event_val(event_trigger)) begin
        func_in_sen_list_trigger_reg = ~func_in_sen_list_trigger_reg;
    end
endmodule
