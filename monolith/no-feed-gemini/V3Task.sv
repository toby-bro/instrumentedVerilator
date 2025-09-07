module BasicTaskHandler (
    input logic [7:0] data_in,
    input logic       enable,
    output logic [7:0] data_out,
    output logic       done
);
    logic [7:0] internal_reg;
    logic       internal_flag_var; 
    logic [7:0] inout_var;
    logic [7:0] ref_var;
    task my_inlined_task(
        input logic [7:0] in_arg,
        output logic [7:0] out_arg,
        inout logic [7:0] inout_arg,
        ref logic [7:0] ref_arg
    );
        out_arg = in_arg + 8'd1;
        inout_arg = inout_arg * 8'd2;
        ref_arg = ref_arg + 8'd3;
        internal_flag_var = 1'b1; 
    endtask
    always_comb begin
        internal_reg = 8'd0;
        inout_var = data_in;
        ref_var = data_in;
        data_out = 8'd0;
        done = 1'b0;
        internal_flag_var = 1'b0; 
        if (enable) begin
            my_inlined_task(data_in, internal_reg, inout_var, ref_var);
            data_out = internal_reg + inout_var + ref_var;
            done = internal_flag_var;
        end else begin
            data_out = 8'd0;
            done = 1'b0;
        end
    end
endmodule
module DpiHandler (
    input logic [31:0] dpi_data_in,
    input logic        dpi_enable,
    output logic [31:0] dpi_data_out
);
    string imported_string;
    chandle ch_handle;
    logic [7:0] unpacked_array [0:3]; 
    import "DPI-C" function int my_import_int_func(input int a, output string s);
    import "DPI-C" task my_export_64bit_task(input logic [63:0] val, inout chandle ch, input string msg);
    import "DPI-C" pure context function chandle my_pure_context_open_array_func(input bit [7:0] arr[]);
    import "DPI-C" task my_export_string_only_task(input string s);
    import "DPI-C" function string my_import_string_func(input string in_str);
    import "DPI-C" function longint my_import_longint_func(input longint l);
    import "DPI-C" function byte my_import_byte_func(input byte b);
    logic [63:0] export_val;
    string export_msg;
    string return_string;
    chandle imported_chandle_out;
    longint imported_longint_res;
    byte imported_byte_res;
    always_comb begin
        dpi_data_out = 32'h0;
        imported_string = "";
        ch_handle = null; 
        export_val = 64'd0;
        export_msg = "";
        return_string = "";
        imported_chandle_out = null;
        imported_longint_res = 0;
        imported_byte_res = 0;
        for (int i=0; i<4; i++) begin 
            unpacked_array[i] = dpi_data_in[7:0] + i;
        end
        if (dpi_enable) begin
            dpi_data_out = my_import_int_func(dpi_data_in, imported_string);
            return_string = my_import_string_func("Another string for import");
            imported_longint_res = my_import_longint_func({32'd0, dpi_data_in});
            imported_byte_res = my_import_byte_func(dpi_data_in[7:0]);
            export_val = {dpi_data_in, dpi_data_in}; 
            export_msg = imported_string; 
            my_export_64bit_task(export_val, ch_handle, export_msg); 
            imported_chandle_out = my_pure_context_open_array_func(unpacked_array);
            my_export_string_only_task("Hello from SV!");
        end
    end
    export "DPI-C" task my_export_64bit_task(input logic [63:0] val, inout chandle ch, input string msg);
    endtask
    export "DPI-C" task my_export_string_only_task(input string s);
    endtask
endmodule
class MyClass;
    logic [15:0] class_member_reg;
    logic [15:0] constructor_init_val;
    logic        method_called_flag;
    int          recursive_depth_limit;
    function new(input logic [15:0] initial_val);
        class_member_reg = initial_val;
        method_called_flag = 1'b0;
        constructor_init_val = 16'hAAAA;
        recursive_depth_limit = 5;
    endfunction
    initial begin
        constructor_init_val = 16'h5555; 
    end
    function automatic logic [15:0] process_data(input logic [15:0] data);
        method_called_flag = 1'b1;
        return class_member_reg + data;
    endfunction
    function automatic int fibonacci(input int n);
        if (n <= 1) return n;
        if (n > recursive_depth_limit) return 0; 
        return fibonacci(n - 1) + fibonacci(n - 2);
    endfunction
endclass
module ClassMethodHandler (
    input logic [15:0] class_data_in,
    input logic        class_enable,
    output logic [15:0] class_data_out
);
    MyClass my_instance; 
    always_comb begin
        class_data_out = 16'h0;
        if (my_instance == null && class_enable) begin
            my_instance = new(class_data_in);
        end
        if (my_instance != null) begin
            class_data_out = my_instance.process_data(class_data_in);
            class_data_out = class_data_out + my_instance.constructor_init_val;
            class_data_out = class_data_out + my_instance.fibonacci(class_data_in[3:0]);
        end
    end
endmodule
module NoInlineRecursiveHandler (
    input logic [7:0] recursive_in,
    input logic       recurse_enable,
    output logic [7:0] recursive_out
);
    (* verilator_no_inline_task *) 
    function automatic logic [7:0] no_inline_func(input logic [7:0] val);
        return val * 8'd2 + 8'd1;
    endfunction
    function automatic logic [7:0] recursive_sum(input logic [3:0] n);
        if (n == 0) return 0;
        if (n == 1) return 1;
        return n + recursive_sum(n - 1);
    endfunction
    always_comb begin
        recursive_out = 8'd0;
        if (recurse_enable) begin
            recursive_out = no_inline_func(recursive_in); 
            recursive_out = recursive_out + recursive_sum(recursive_in[3:0]); 
        end
    end
endmodule
module ArgHandler (
    input int arg_handler_in,
    input logic arg_handler_enable,
    output int arg_handler_out
);
    int local_temp_val;
    task process_defaults (
        input int a = 10,                 
        input int b = local_temp_val,     
        output int sum_out,
        input string message = "DefaultMsg" 
    );
        sum_out = a + b;
    endtask
    task sformat_logger(input int id, /* verilator sformat */ input string format_str);
    endtask
    always_comb begin
        arg_handler_out = 0;
        local_temp_val = arg_handler_in + 5; 
        if (arg_handler_enable) begin
            int sum_result;
            string log_message;
            process_defaults(.sum_out(sum_result));
            arg_handler_out = arg_handler_out + sum_result;
            process_defaults(.b(arg_handler_in), .sum_out(sum_result));
            arg_handler_out = arg_handler_out + sum_result;
            process_defaults(20, arg_handler_in + 1, sum_result);
            arg_handler_out = arg_handler_out + sum_result;
            process_defaults(30, arg_handler_in + 2, sum_result, "FullOverride");
            arg_handler_out = arg_handler_out + sum_result;
            sformat_logger(arg_handler_in, "Log value: %d, Message: %s from ArgHandler");
        end
    end
endmodule
module LoopWithHandler (
    input logic clk,
    input logic reset,
    input logic [3:0] loop_count_in,
    output logic [7:0] loop_sum_out,
    output logic sen_list_flag 
);
    logic [7:0] sum_reg;
    function automatic logic [7:0] calculate_sum_with(input logic [3:0] count);
        logic [7:0] local_sum = 0;
        local_sum = count with (sum(item) for (int item = 0; item <= count; item++)); 
        return local_sum;
    endfunction
    function automatic logic check_clk_transition(input logic clk_signal);
        return clk_signal;
    endfunction
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            sum_reg = 0;
            loop_sum_out = 0;
        end else begin
            sum_reg = calculate_sum_with(loop_count_in);
            loop_sum_out = sum_reg;
        end
    end
    always_comb begin
        int i_while = 0;
        logic [7:0] temp_while_sum = 0;
        while (i_while < loop_count_in) begin 
            temp_while_sum = temp_while_sum + i_while;
            i_while++;
        end
        sen_list_flag = (temp_while_sum > 0); 
    end
    always_comb @(posedge clk or posedge check_clk_transition(clk)) begin
        sen_list_flag = sen_list_flag;
    end
endmodule
