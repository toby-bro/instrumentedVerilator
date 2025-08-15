`timescale 1ns/1ps
module TimingDelays (
    input logic clk_in,
    input logic rst_in,
    input int in_val,
    input real in_real_val,
    input int int_delay_val,
    input int idx_in,
    output wire [7:0] out_net_delay,
    output wire real out_real_delay,
    output reg [7:0] out_intra_delay,
    output reg [7:0] out_arr_idx_dly [0:7],
    output wire int out_int_delay_val_pass
);
    assign #1 out_net_delay = in_val;
    assign #1.0 out_real_delay = in_real_val;
    always_ff @(posedge clk_in or posedge rst_in) begin
        if (rst_in) begin
            out_intra_delay <= 8'b0;
        end else begin
            out_intra_delay <= #int_delay_val in_val;
        end
    end
    assign out_int_delay_val_pass = int_delay_val;
    always_comb begin
        logic [2:0] safe_idx = idx_in[2:0];
        out_arr_idx_dly[safe_idx] = #1 in_val[7:0];
    end
endmodule
module EventWaitControls (
    input logic clk_in,
    input logic rst_in,
    input logic cond_in_a,
    input logic cond_in_b,
    output wire out_flag_a,
    output wire out_flag_b,
    output wire out_event_triggered,
    output wire out_wait_task_result
);
    event my_event;
    logic local_wait_flag_reg;
    logic internal_wait_test_cond_reg;
    reg out_flag_a_r;
    reg out_flag_b_r;
    reg out_event_triggered_r;
    reg out_wait_task_result_r;
    assign out_flag_a = out_flag_a_r;
    assign out_flag_b = out_flag_b_r;
    assign out_event_triggered = out_event_triggered_r;
    assign out_wait_task_result = out_wait_task_result_r;
    always @(my_event) begin
        out_event_triggered_r <= ~out_event_triggered_r;
    end
    always_ff @(posedge clk_in or posedge rst_in) begin
        if (rst_in) begin
            out_flag_b_r <= 1'b0;
        end else begin
            out_flag_b_r <= cond_in_b;
        end
    end
    task automatic run_wait_tests(output logic task_output);
        task_output = 1'b0;
        internal_wait_test_cond_reg = 1'b1;
        wait (internal_wait_test_cond_reg);
        task_output = 1'b1;
        local_wait_flag_reg = 1'b1;
        wait (local_wait_flag_reg);
        task_output = task_output + 1'b1;
    endtask
    initial begin
        out_event_triggered_r = 1'b0;
        out_flag_a_r = 1'b0;
        local_wait_flag_reg = 1'b0;
        internal_wait_test_cond_reg = 1'b0;
        run_wait_tests(out_wait_task_result_r);
        out_flag_a_r = 1'b1;
    end
    always @(posedge clk_in) begin
        -> my_event;
    end
endmodule
class MyBaseClass;
    virtual task automatic process_base_delay(input int delay_val, output int out_data_task, input logic dynamic_wait_cond_arg);
        wait (dynamic_wait_cond_arg + 1);
        out_data_task = delay_val + 1;
    endtask
endclass
class MyDerivedClass extends MyBaseClass;
    task automatic process_base_delay(input int delay_val, output int out_data_task, input logic dynamic_wait_cond_arg);
        wait (dynamic_wait_cond_arg + 1);
        out_data_task = delay_val * 2 + 10;
    endtask
    task automatic call_base_from_derived(input int d_val, output int out_data_task, input logic dynamic_wait_cond_arg);
        wait (dynamic_wait_cond_arg + 1);
        super.process_base_delay(d_val, out_data_task, dynamic_wait_cond_arg);
    endtask
endclass
module ClassMethodTiming (
    input logic clk_in,
    input int initial_delay_base,
    input int initial_delay_derived,
    input int call_base_from_derived_val,
    input logic dynamic_wait_control,
    output int dummy_output_class
);
    MyBaseClass base_inst;
    MyDerivedClass derived_inst;
    reg dummy_output_class_r;
    assign dummy_output_class = dummy_output_class_r;
    initial begin
        base_inst = new();
        derived_inst = new();
        dummy_output_class_r = 0;
        base_inst.process_base_delay(initial_delay_base, dummy_output_class_r, dynamic_wait_control);
        dummy_output_class_r = initial_delay_base;
        derived_inst.process_base_delay(initial_delay_derived, dummy_output_class_r, dynamic_wait_control);
        dummy_output_class_r = dummy_output_class_r + initial_delay_derived;
        derived_inst.call_base_from_derived(call_base_from_derived_val, dummy_output_class_r, dynamic_wait_control);
        dummy_output_class_r = dummy_output_class_r + call_base_from_derived_val;
    end
endmodule
module ForkJoinExample (
    input logic clk_in,
    input int data_in_a,
    input int data_in_b,
    input logic cond_disable_fork,
    output wire int sum_out,
    output wire int product_out,
    output wire int fork_status_out
);
    reg sum_out_r;
    reg product_out_r;
    reg fork_status_out_r;
    assign sum_out = sum_out_r;
    assign product_out = product_out_r;
    assign fork_status_out = fork_status_out_r;
    int local_fork_var;
    initial begin
        sum_out_r = 0;
        product_out_r = 1;
        fork_status_out_r = 0;
        local_fork_var = 100;
        fork
            begin : add_task_block
                sum_out_r = data_in_a + data_in_b + local_fork_var;
                fork_status_out_r = fork_status_out_r + 1;
            end
            begin : mul_task_block
                product_out_r = data_in_a * data_in_b * 2;
                fork_status_out_r = fork_status_out_r + 2;
            end
        join
        fork_status_out_r = fork_status_out_r + 4;
        fork
            begin : any_task_1
                fork_status_out_r = fork_status_out_r + 10;
            end
            begin : any_task_2
                fork_status_out_r = fork_status_out_r + 20;
            end
        join_any
        if (cond_disable_fork) disable fork;
        fork
            begin : none_task_1
                fork_status_out_r = fork_status_out_r + 100;
            end
            begin : none_task_2
                fork_status_out_r = fork_status_out_r + 200;
            end
        join_none
        wait fork;
        fork_status_out_r = fork_status_out_r + 400;
    end
endmodule
module InitialAlwaysAdvanced (
    input logic clk_in,
    input logic reset_n,
    input int fact_input,
    output wire int fact_output
);
    reg fact_output_r;
    assign fact_output = fact_output_r;
    initial begin : init_block
        fact_output_r = 0;
    end
    reg [7:0] count;
    always_ff @(posedge clk_in or negedge reset_n) begin
        if (!reset_n) begin
            count <= 8'b0;
        end else begin
            count <= count + 1;
        end
    end
    function automatic integer compute_factorial(input int n);
        integer result = 1;
        if (n < 0) result = 0;
        else begin
            for (int i = 1; i <= n; i++) begin
                result = result * i;
            end
        end
        return result;
    endfunction
    always_ff @(posedge clk_in) begin
        fact_output_r <= compute_factorial(fact_input);
    end
endmodule
