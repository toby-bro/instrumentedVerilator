module BasicLogic (
    input logic [7:0] in_data_basic,
    output logic [15:0] out_result_basic
);
    logic [7:0] local_reg = 8'hAA;
    int integer_var = 12345;
    real real_var = 3.14159;
    string string_var = "Hello SystemVerilog";
    const int MY_CONST_INT = 100;
    always_comb begin : named_block_expr
        logic [7:0] temp_val_a;
        logic [7:0] temp_val_b;
        logic [7:0] accessed_var;
        temp_val_a = in_data_basic + local_reg;
        temp_val_b = 8'hFF - in_data_basic;
        out_result_basic = {temp_val_a, temp_val_b};
        out_result_basic[7:0] = temp_val_a[7:0];
        integer_var = int'(temp_val_a) + int'(temp_val_b);
        real_var = real'(integer_var) / 2.0;
        accessed_var = local_reg;
    end
    function automatic int get_sum(int a, int b);
        int sum;
        sum = a + b;
        return sum;
    endfunction
    task automatic assign_output(logic [15:0] value);
        logic [15:0] internal_value;
        internal_value = value;
        out_result_basic = internal_value;
    endtask
    always_comb begin
        int sum_val;
        logic [15:0] assign_val;
        sum_val = get_sum(integer_var, 100);
        assign_val = {sum_val[7:0], sum_val[15:8]};
        assign_output(assign_val);
    end
endmodule
module DataStructures (
    input logic in_clock_ds,
    output logic [15:0] out_array_sum
);
    typedef struct packed {
        logic [7:0] field_a;
        int         field_b;
    } my_struct_t;
    my_struct_t unpacked_array[4];
    int dynamic_array[];
    int associative_array[*];
    int queue_var[$];
    typedef enum logic [1:0] {
        STATE_IDLE = 2'b00,
        STATE_BUSY = 2'b01,
        STATE_DONE = 2'b10
    } fsm_state_t;
    fsm_state_t current_state = STATE_IDLE;
    class MyFwdClass;
    endclass
    typedef MyFwdClass MyFwdClassTypedef;
    int init_fixed_array[3] = '{10, 20, 30};
    always_comb begin : data_ops_block
        my_struct_t s_temp;
        logic [31:0] stream_in = 32'h12345678;
        logic [7:0] byte_array[4];
        s_temp.field_a = in_clock_ds ? 8'hF0 : 8'h0F;
        s_temp.field_b = 500;
        unpacked_array[0] = s_temp;
        dynamic_array = new[2];
        dynamic_array[0] = 100;
        dynamic_array[1] = 200;
        associative_array["key1"] = 1;
        associative_array["key2"] = 2;
        queue_var.push_back(300);
        queue_var.push_back(400);
        out_array_sum = unpacked_array[0].field_a + dynamic_array[0] + associative_array["key1"] + queue_var[0];
        byte_array = {>>8{stream_in}};
    end
    function automatic int sum_array(int array_in[]);
        int total = 0;
        for (int i = 0; i < array_in.size(); i++) begin : loop_sum
            total += array_in[i];
        end
        return total;
    endfunction
    always_comb begin
        int temp_sum;
        temp_sum = sum_array(dynamic_array);
    end
endmodule
module ClassFuncTaskDPI (
    input logic in_enable_dpi,
    output logic out_status_dpi
);
    import "DPI-C" function int c_add_one(int val);
    import "DPI-C" function int c_recursive_func(int count);
    import "DPI-C" function void c_call_void();
    class MyBaseClass;
        protected int m_data;
        function new();
            m_data = 0;
        endfunction
        virtual function int get_data();
            return m_data;
        endfunction
    endclass
    class MyDerivedClass extends MyBaseClass;
        function new();
            super.new();
            m_data = 10;
        endfunction
        function int get_data();
            return m_data + 1;
        endfunction
        function automatic int factorial(int n);
            if (n <= 1) return 1;
            return n * this.factorial(n - 1);
        endfunction
        task automatic count_down(int n);
            if (n > 0) begin : recursive_task_block
                fork
                join
                this.count_down(n - 1);
            end
        endtask
        function logic check_null_handle(MyDerivedClass handle);
            if (handle == null) begin
                return 1'b1;
            end
            return 1'b0;
        endfunction
    endclass
    MyDerivedClass my_obj;
    MyDerivedClass null_obj = null;
    always_comb begin : class_proc_block
        int result_dpi;
        int fact_val;
        logic is_null;
        if (my_obj == null) begin
            my_obj = new();
        end
        result_dpi = c_add_one(my_obj.get_data());
        fact_val = my_obj.factorial(5);
        my_obj.count_down(3);
        is_null = my_obj.check_null_handle(null_obj);
        out_status_dpi = in_enable_dpi && (result_dpi > 0) && !is_null;
        result_dpi = c_recursive_func(3);
        c_call_void();
    end
endmodule
interface MyInterface (input logic clk_iface, input logic reset_n_iface);
    logic [7:0] data_if;
    logic req_if, ack_if;
    modport Master (
        output data_if,
        output req_if,
        input ack_if,
        input clk_iface,
        input reset_n_iface,
        export func_iface_master
    );
    modport Slave (
        input data_if,
        input req_if,
        output ack_if,
        input clk_iface,
        input reset_n_iface,
        import func_iface_slave
    );
    function automatic int func_iface_master(int in_val);
        return in_val + 1;
    endfunction
    function automatic int func_iface_slave(int in_val);
        return in_val - 1;
    endfunction
endinterface
module TopModule (
    input logic clk_top,
    input logic rst_top,
    output logic [7:0] out_val_top
);
    MyInterface my_if(.clk_iface(clk_top), .reset_n_iface(rst_top));
    module InnerModule # (
        parameter WIDTH = 8
    ) (
        input logic [WIDTH-1:0] in_data_inner,
        output logic [WIDTH-1:0] out_data_inner_mod
    );
        assign out_data_inner_mod = in_data_inner + 1;
    endmodule
    InnerModule #(.WIDTH(8)) inner_inst (.in_data_inner(my_if.data_if), .out_data_inner_mod(out_val_top));
    always_comb begin : current_scope
        logic [7:0] var_in_scope = 8'hC0;
        my_if.data_if = var_in_scope;
    end
    always_comb begin
        int master_func_res;
        my_if.req_if = 1'b1;
        my_if.ack_if = 1'b0;
        master_func_res = my_if.Master.func_iface_master(10);
    end
endmodule
module ControlAssertions (
    input logic clk_ca,
    input logic rst_n_ca,
    input logic in_data_assert,
    output logic out_feedback_ca
);
    logic [3:0] counter_ff;
    logic [3:0] comb_var;
    always_ff @(posedge clk_ca or negedge rst_n_ca) begin : ff_block_ca
        if (!rst_n_ca) begin
            counter_ff <= 4'b0;
        end else begin
            counter_ff <= counter_ff + 1;
        end
        out_feedback_ca <= counter_ff[0];
    end
    always_comb begin : comb_block_ca
        begin : my_local_scope
            logic temp_local_var;
            temp_local_var = in_data_assert;
            comb_var = counter_ff + (temp_local_var ? 1 : 0);
        end
        assert property (@(posedge clk_ca) in_data_assert |=> out_feedback_ca);
        cover property (@(posedge clk_ca) in_data_assert && out_feedback_ca);
    end
    covergroup my_cg @(posedge clk_ca);
        option.per_instance = 1;
        a_cp: coverpoint in_data_assert;
        b_cp: coverpoint counter_ff {
            bins zero = (0);
            bins other = default;
        }
    endgroup
    my_cg cg_inst = new();
endmodule
module SystemTasksAttributes (
    input logic [7:0] in_value_sys,
    output logic [7:0] out_value_sys
);
    string format_str;
    int scanned_val;
    string sscan_in_str = "Value: 456";
    logic [1:0] sel_pragma_in = 2'b00;
    logic [7:0] data_out_pragma;
    (* verilator_my_custom_attr = "some_value" *) logic [7:0] attributed_signal;
    always_comb begin : main_calculation_block
        format_str = $sformatf("Input value is %0d", in_value_sys);
        (* full_case, parallel_case *)
        case (sel_pragma_in)
            2'b00: data_out_pragma = 8'h01;
            2'b01: data_out_pragma = 8'h02;
            2'b10: data_out_pragma = 8'h04;
            default: data_out_pragma = 8'hFF;
        endcase
        attributed_signal = in_value_sys;
        out_value_sys = data_out_pragma + attributed_signal;
    end
    always_comb begin : display_monitor_block
        if (in_value_sys == 8'h0) begin
            $info("Input value is zero. (%0s)", format_str);
        end else if (in_value_sys == 8'hFF) begin
            $warning("Input value is max. (%0s)", format_str);
        end else if (in_value_sys == 8'hEE) begin
            $error("Input value is specific error. (%0s)", format_str);
        end else if (in_value_sys == 8'hDD) begin
            $fatal(1, "Input value is fatal. (%0s)", format_str);
        end
        monitor_control_task(in_value_sys[0]);
    end
    task automatic monitor_control_task(logic off_val);
        if (off_val) $monitoroff;
    endtask
    function automatic void process_scans();
        void'($sscanf(sscan_in_str, "Value: %d", scanned_val));
    endfunction
    always_comb begin : sscanf_block
        process_scans();
    end
endmodule
