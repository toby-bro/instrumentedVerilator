module Mod_InliningAndAssignments (
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] internal_reg;
    wire [7:0] internal_wire;
    assign internal_wire = data_in + 1;
    task my_simple_task(input logic [7:0] val_in, output logic [7:0] val_out);
        val_out = val_in * 2;
        internal_reg = val_in;
    endtask
    function logic [7:0] my_simple_function(input logic [7:0] val_in_func);
        return val_in_func + 3;
    endfunction
    always_comb begin
        logic [7:0] task_local_output;
        logic [7:0] func_result;
        my_simple_task(internal_wire, task_local_output);
        data_out = task_local_output;
        func_result = my_simple_function(data_in);
        data_out = data_out + func_result;
        void'(my_simple_function(data_in[3:0]));
    end
endmodule
module Mod_NoInlinePragma (
    input int count_in,
    output int result_out
);
    int local_counter = 0;
    (* verilator no_inline_task *)
    task no_inline_task(input int start_val, output int end_val);
        end_val = start_val + 10;
        local_counter = local_counter + 1;
    endtask
    (* verilator no_inline_task *)
    function int no_inline_func(input int input_val);
        local_counter = local_counter + 2;
        return input_val * 2;
    endfunction
    task complex_args_task(input int i_in, inout int io_val, ref int r_val);
        io_val = io_val + i_in;
        r_val = r_val + 5;
    endtask
    always_comb begin
        int task_out;
        int func_res;
        int inout_arg = count_in;
        int ref_arg = count_in + 1;
        no_inline_task(count_in, task_out);
        func_res = no_inline_func(count_in + 1);
        complex_args_task(count_in, inout_arg, ref_arg);
        result_out = task_out + func_res + inout_arg + ref_arg;
    end
endmodule
module Mod_DPIImport (
    input logic [31:0] dpi_data_in,
    input chandle dpi_handle_in,
    input int dpi_unpacked_arr_in [3],
    input int dpi_fixed_arr_in [5],
    output string dpi_string_out
);
    import "DPI-C" function int my_dpi_import_func(
        input bit [7:0] byte_in,
        input logic [15:0] logic_vec_in,
        input int int_in,
        input string str_in,
        input chandle handle_in,
        input int unpacked_arr_in [3],
        output int out_val
    );
    import "DPI-C" task my_dpi_import_task(
        input logic [63:0] long_vec_in,
        input int open_arr_in [*]
    );
    always_comb begin
        int func_out_val;
        int func_ret;
        string temp_str = "Hello DPI";
        func_ret = my_dpi_import_func(
            dpi_data_in[7:0],
            dpi_data_in[23:8],
            dpi_data_in[31:24],
            temp_str,
            dpi_handle_in,
            dpi_unpacked_arr_in,
            func_out_val
        );
        my_dpi_import_task(dpi_data_in, dpi_fixed_arr_in);
        dpi_string_out = $sformatf("%0d-%0d", func_ret, func_out_val);
    end
endmodule
module Mod_DPIExport (
    input int exp_val_in,
    output logic [63:0] exp_ret_out,
    output logic [63:0] exported_state_out
);
    logic [63:0] current_state_var;
    export "DPI-C" function my_dpi_export_func;
    function logic [63:0] my_dpi_export_func(input int multiplier);
        return $unsigned(exp_val_in) * multiplier;
    endfunction
    export "DPI-C" context task my_dpi_export_task;
    task my_dpi_export_task(input int add_val, output logic [63:0] new_state);
        new_state = current_state_var + add_val;
    endtask
    always_comb begin
        logic [63:0] task_next_state;
        current_state_var = $unsigned(exp_val_in);
        exp_ret_out = my_dpi_export_func(2);
        my_dpi_export_task(exp_val_in, task_next_state);
        exported_state_out = task_next_state;
    end
endmodule
module Mod_ClassWithInitAutomatic (
    input logic class_init_en,
    output logic class_val_out
);
    class MyClass;
        logic [7:0] internal_data;
        int counter;
        initial automatic begin
            internal_data = 8'hAA;
            counter = 0;
        end
        function new();
            internal_data = internal_data + 1;
            counter = counter + 1;
        endfunction
        function logic [7:0] get_data();
            return internal_data;
        endfunction
        function int get_counter();
            return counter;
        endfunction
    endclass
    MyClass my_instance;
    always_comb begin
        if (class_init_en) begin
            my_instance = new();
        end else begin
            my_instance = null;
        end
        if (my_instance != null) begin
            class_val_out = (my_instance.get_data() == 8'hAB && my_instance.get_counter() == 1);
        end else begin
            class_val_out = 1'b0;
        end
    end
endmodule
module Mod_RecursiveAndControl (
    input int recurse_depth,
    output int factorial_out,
    input logic [7:0] sens_var_a_in,
    input logic [7:0] sens_var_b_in,
    output logic [7:0] sens_result_out
);
    function automatic int factorial(input int n);
        if (n <= 1) begin
            return 1;
        end else begin
            return n * factorial(n - 1);
        end
    endfunction
    task iterative_sum(input int max_val, output int sum_res);
        int i = 0;
        sum_res = 0;
        while (i <= max_val) begin
            sum_res = sum_res + i;
            i++;
        end
    endtask
    function int get_fixed_value();
        return 10;
    endfunction
    always @(sens_var_a_in or sens_var_b_in or get_fixed_value()) begin
        sens_result_out = sens_var_a_in + sens_var_b_in + get_fixed_value();
    end
    always_comb begin
        int temp_sum;
        int fact_val;
        fact_val = factorial(recurse_depth);
        iterative_sum(recurse_depth, temp_sum);
        factorial_out = fact_val + temp_sum;
    end
endmodule
module Mod_NamedDefaultArgs (
    input int a_in,
    input int b_in,
    output int sum_out
);
    task compute_sum_task(
        input int arg1 = 10,
        input int arg2,
        input int arg3 = 20,
        input int final_arg
    );
        int intermediate_sum;
        intermediate_sum = arg1 + arg2 + arg3 + final_arg;
        sum_out = intermediate_sum;
    endtask
    always_comb begin
        compute_sum_task(a_in, b_in, 5, 1);
        compute_sum_task(.arg2(a_in + b_in), .final_arg(10), .arg1(a_in * 2));
    end
endmodule
module Mod_RandomizeWith (
    input int seed_in,
    output int rand_val_out
);
    class MyRandClass;
        rand int value_a;
        rand int value_b;
        constraint c1 { value_a > 0; value_b < 100; }
        constraint c2 { value_a + value_b == 50; }
        function void do_randomize();
            this.randomize();
        endfunction
        function void do_randomize_with_clause(input int limit);
            this.randomize() with {
                value_a < limit;
            };
        endfunction
    endclass
    MyRandClass rand_inst;
    always_comb begin
        if (seed_in != 0) begin
            rand_inst = new();
            rand_inst.srandom(seed_in);
            rand_inst.do_randomize();
            rand_inst.do_randomize_with_clause(seed_in + 10);
            rand_val_out = rand_inst.value_a + rand_inst.value_b;
        end else begin
            rand_val_out = 0;
            rand_inst = null;
        end
    end
endmodule
