`timescale 1ns / 1ps
module ModTimingBasics (
    input logic clk,
    input logic reset_n,
    input logic data_in,
    output logic data_out_reg,
    output logic initial_done
);
    logic internal_wait_cond;
    always @(posedge clk or negedge reset_n) begin : always_block_proc
        if (!reset_n) begin
            data_out_reg <= 1'b0;
            internal_wait_cond = 1'b0;
        end else begin
            #10ps data_out_reg <= data_in;
            if (data_in == 1'b1) begin
                internal_wait_cond = 1'b1;
            end else begin
                wait(internal_wait_cond);
                data_out_reg <= ~data_out_reg;
                internal_wait_cond = 1'b0;
            end
        end
    end
    initial begin : initial_proc
        #500ps;
        initial_done = 1'b1;
    end
endmodule
module ModForking (
    input logic clk,
    input logic fork_start,
    input logic [7:0] fork_val_in,
    input logic cond_a,
    input logic cond_b,
    output logic [7:0] fork_sum_out,
    output logic fork_status
);
    logic [7:0] local_sum;
    logic       local_status;
    always @(posedge clk) begin : always_block_fork
        if (fork_start) begin
            local_sum = 8'h00;
            local_status = 1'b0;
            fork : fj_none_example
                begin : proc_1_none
                    #1ns;
                    local_sum = local_sum + fork_val_in;
                    disable fork;
                end
                begin : proc_2_none
                    @(posedge clk);
                    local_sum = local_sum - fork_val_in;
                    wait fork;
                end
            join_none
            fork_status = 1'b1;
            fork : fj_example
                begin : proc_1_join
                    #2ns;
                    local_sum = local_sum + 1;
                end
                begin : proc_2_join
                    @(posedge cond_a);
                    local_sum = local_sum + 2;
                end
            join
            fork : fj_any_example
                begin : proc_1_any
                    #3ns;
                    local_sum = local_sum + 10;
                end
                begin : proc_2_any
                    @(posedge cond_b);
                    local_sum = local_sum + 20;
                end
            join_any
            fork_sum_out = local_sum;
        end
    end
endmodule
module ModAssignDelays (
    input logic clk,
    input logic [7:0] in_val,
    input logic [2:0] idx_val,
    input logic [7:0] lhs_val,
    output logic [7:0] assign_out,
    output logic [7:0] array_data_out [0:7]
);
    logic [7:0] reg_a, reg_b;
    assign #2ps assign_out = in_val;
    always @(posedge clk) begin : assign_block
        reg_b = in_val + 1;
        reg_a = #3ns reg_b;
        array_data_out[idx_val] = #1ns lhs_val;
    end
endmodule
module ModTaskFuncTiming (
    input logic clk,
    input logic task_input_data,
    input logic [7:0] func_input_data,
    output logic task_output_data,
    output logic [7:0] func_output_data
);
    task automatic my_timed_task;
        input bit data;
        output bit result;
        @(posedge clk);
        #1ns;
        result = data;
    endtask
    task automatic my_calling_task;
        input bit data_in;
        output bit task_res;
        my_timed_task(data_in, task_res);
    endtask
    function automatic bit my_combinational_function;
        input bit data_in;
        return data_in;
    endfunction
    logic task_trigger_reg;
    logic my_calling_task_result_reg;
    always @(posedge clk) begin
        if (task_input_data) begin
            my_timed_task(task_input_data, task_trigger_reg);
            task_output_data = task_trigger_reg;
        end else begin
            task_output_data = 1'b0;
        end
        my_calling_task(func_input_data[0], my_calling_task_result_reg);
        func_output_data = {7'b0, my_calling_task_result_reg};
    end
endmodule
module ModClassTiming (
    input logic clk,
    input logic obj_in_val,
    output logic obj_out_val
);
    class MyBaseClass;
        virtual task timed_method(input bit enable, output bit result);
            #1ns;
            result = enable;
        endtask
    endclass
    class MyDerivedClass extends MyBaseClass;
        logic internal_val;
        function new();
            internal_val = 1'b0;
        endfunction
        virtual task timed_method(input bit enable, output bit result);
            @(posedge clk);
            internal_val = enable;
            result = internal_val;
        endtask
    endclass
    MyDerivedClass my_object_inst;
    always @(posedge clk) begin : class_instance_block
        if (my_object_inst == null) begin
            my_object_inst = new();
        end
        my_object_inst.timed_method(obj_in_val, obj_out_val);
    end
endmodule
module ModAdvWait (
    input logic clk,
    input logic condition_var,
    output logic wait_result_out
);
    event my_event;
    always @(posedge clk) begin : wait_block
        wait_result_out = 1'b0;
        wait(1'b1) begin
            wait_result_out = 1'b1;
        end
        wait(1'b0) begin
            wait_result_out = 1'b0;
        end
        wait(condition_var) begin
            wait_result_out = 1'b1;
        end
        if (condition_var) begin
            -> my_event;
        end
        wait(my_event.triggered) begin
            wait_result_out = 1'b1;
        end
    end
endmodule
