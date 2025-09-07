module SimpleDeclarationsAndAssignments (
    input logic       i_clk,
    input logic [7:0] i_data_in,
    output logic [7:0] o_data_out
);
    parameter int PARAM_WIDTH = 8;
    parameter string MESSAGE = "Hello_Verilator";
    logic [PARAM_WIDTH-1:0] internal_reg;
    wire [7:0] internal_wire;
    supply0 GND_net;
    supply1 VCC_net;
    assign internal_wire = i_data_in + PARAM_WIDTH;
    assign o_data_out = internal_reg + 1;
    always_comb begin
        string local_message;
        if (i_clk) begin
            internal_reg = i_data_in;
        end else begin
            internal_reg = 8'h00;
        end
        local_message = MESSAGE;
    end
endmodule
module ArrayAndSelects (
    input logic [31:0] i_input_vec,
    input int          i_addr,
    output logic [7:0] o_byte_out
);
    logic [7:0] packed_array [3:0];
    logic unpacked_array [4][8];
    logic [15:0] dynamic_array [];
    logic [7:0] data_queue [$];
    logic [3:0] assoc_array [string];
    logic wildcard_assoc_array [*];
    logic [4:0] multi_dim_arr [2:0][1:0];
    typedef logic dyn_arr_typedef [];
    typedef logic multi_dim_typedef [1:0][2:0];
    typedef logic assoc_arr_typedef [string];
    dyn_arr_typedef my_dyn_arr;
    multi_dim_typedef my_multi_dim_arr_typed;
    assoc_arr_typedef my_assoc_arr_typed;
    always_comb begin
        logic [31:0] temp_vec_sum;
        o_byte_out = 8'h00;
        packed_array[0] = i_input_vec[7:0];
        packed_array[1] = i_input_vec[15:8];
        packed_array[2] = i_input_vec[23:16];
        packed_array[3] = i_input_vec[31:24];
        if (i_addr < 4) begin
            temp_vec_sum = i_input_vec + i_input_vec;
            o_byte_out = temp_vec_sum[i_addr*8 +: 8];
        end else begin
            o_byte_out = 8'hFF;
        end
        dynamic_array = new[2];
        dynamic_array[0] = 16'hAAAA;
        dynamic_array[1] = 16'hBBBB;
        data_queue.push_back(i_input_vec[7:0]);
        data_queue.push_front(i_input_vec[15:8]);
        void'(data_queue.pop_front());
        assoc_array["key1"] = i_input_vec[3:0];
        wildcard_assoc_array[1'b0] = i_input_vec[0];
        multi_dim_arr[0][0] = 5'b00001;
        my_dyn_arr = new[1];
        my_dyn_arr[0] = 1'b1;
        my_multi_dim_arr_typed[0][0] = 1'b0;
        my_assoc_arr_typed["test_key"] = i_input_vec[3:0];
    end
endmodule
module AdvancedTypesAndLifetimes (
    input real      i_real_in,
    input longint   i_long_in,
    output shortint o_short_out
);
    int         my_int;
    integer     my_integer;
    byte        my_byte;
    shortint    my_shortint;
    longint     my_longint;
    real        my_real;
    shortreal   my_shortreal;
    var logic [3:0] var_logic_val;
    typedef logic [63:0] my_wide_bus_t;
    my_wide_bus_t wide_data_bus;
    class MyClass;
        logic [7:0] data;
        function new();
            this.data = 8'hCC;
        endfunction
    endclass
    function static int static_func (input int a);
        int val;
        static int static_val;
        static_val = static_val + a;
        val = a;
        return static_val + val;
    endfunction
    function automatic int automatic_func (input int a);
        int val;
        val = a + 1;
        return val;
    endfunction
    (* full_case, parallel_case *) logic [1:0] attr_signal;
    parameter int ATTRIB_PARAM = 10;
    MyClass my_instance;
    always_comb begin
        my_int = 10;
        my_integer = 20;
        my_byte = 30;
        my_shortint = shortint'(i_long_in);
        my_longint = i_long_in;
        my_real = i_real_in;
        my_shortreal = shortreal'(i_real_in);
        var_logic_val = 4'hF;
        wide_data_bus = 64'hFEEDFACE_BEEFCAFE;
        my_instance = new();
        o_short_out = shortint'(my_instance.data);
        attr_signal = 2'b01;
        void'(static_func(1));
        void'(automatic_func(2));
    end
endmodule
module PortDeclarationsAndArgumentLists (
    input logic i_a,
    output logic o_b,
    inout  wire  io_c
);
    logic non_ansi_input_internal;
    logic non_ansi_output_internal;
    logic non_ansi_inout_internal;
    logic internal_logic;
    typedef struct packed {
        logic [3:0] s_f1;
        logic [3:0] s_f2;
    } my_struct_t;
    function logic [7:0] my_complex_func (
        input logic [3:0] arg1,
        input logic [3:0] arg2
    );
        return {arg1, arg2} + 8'h01;
    endfunction
    task my_simple_task (input logic [7:0] task_data);
        internal_logic = task_data[0];
    endtask
    task my_expr_task (
        input logic [7:0] expr_arg1,
        input int expr_arg2,
        output logic [7:0] out_expr_res
    );
        out_expr_res = expr_arg1 + expr_arg2;
    endtask
    function automatic logic [7:0] struct_arg_func (input my_struct_t s_in);
        return {s_in.s_f1, s_in.s_f2};
    endfunction
    assign o_b = i_a;
    assign io_c = 1'bZ;
    always_comb begin
        logic [7:0] func_res;
        logic [7:0] task_expr_res;
        my_struct_t s_local;
        logic [7:0] struct_func_res;
        func_res = my_complex_func(i_a ? 4'hF : 4'h0, io_c ? 4'hA : 4'h5);
        non_ansi_output_internal = func_res[0];
        my_simple_task(func_res);
        my_expr_task(func_res + 8'h10, $clog2(8) + 1, task_expr_res);
        non_ansi_inout_internal = task_expr_res[0];
        non_ansi_input_internal = i_a | io_c;
        s_local.s_f1 = func_res[3:0];
        s_local.s_f2 = task_expr_res[3:0];
        struct_func_res = struct_arg_func(s_local);
        internal_logic = struct_func_res[0];
    end
endmodule
module NonAnsiPortModule (
    i_val,
    o_res,
    non_ansi_input_port,
    non_ansi_output_port,
    non_ansi_inout_port
);
    input logic [7:0] i_val;
    output logic [7:0] o_res;
    input logic non_ansi_input_port;
    output logic non_ansi_output_port;
    inout wire non_ansi_inout_port;
    logic internal_var;
    assign o_res = i_val + internal_var;
    assign non_ansi_output_port = i_val[0];
    assign non_ansi_inout_port = 1'bZ;
    always_comb begin
        internal_var = non_ansi_input_port ? 8'd10 : 8'd20;
    end
endmodule
module UntypedNonAnsiPortModule (
    clk_in,
    data_out,
    data_inout
);
    input logic clk_in;
    output reg data_out;
    inout wire data_inout;
    assign data_inout = clk_in ? 1'b1 : 1'b0;
    always_comb begin
        data_out = clk_in;
    end
endmodule
