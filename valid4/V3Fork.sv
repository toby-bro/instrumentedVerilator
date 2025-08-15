module ForkBasic (
    input logic [7:0] in_data,
    output logic [7:0] out_result
);
    class MySharedStateBasic;
        logic [7:0] proc_local_var;
        logic [7:0] shared_var_proc;
        logic [7:0] temp_out_result;
    endclass
    always_comb begin : main_proc_block
        automatic MySharedStateBasic state_h = new();
        state_h.proc_local_var = 8'd20;
        state_h.shared_var_proc = in_data;
        state_h.temp_out_result = 8'd0;
        fork : my_first_fork_jn
            automatic logic [7:0] fork_local_var = 8'd30;
            state_h.proc_local_var = state_h.proc_local_var + 1;
            state_h.shared_var_proc = state_h.shared_var_proc + 2;
            fork_local_var = fork_local_var + 5;
            state_h.temp_out_result = state_h.proc_local_var + state_h.shared_var_proc + fork_local_var;
        join_none
        out_result = state_h.temp_out_result;
    end
endmodule
module ForkTimingControl (
    input bit clk,
    input bit reset_n,
    input logic [3:0] in_val,
    output logic [3:0] out_val
);
    logic [3:0] reg_state_val;
    class MyTimingState;
        logic [3:0] auto_b_proc;
        logic [3:0] auto_c_proc;
        logic [3:0] next_out_val;
    endclass
    always_ff @(posedge clk) begin : main_proc_block
        automatic MyTimingState timing_state_h = new();
        logic [3:0] captured_in_val = in_val;
        timing_state_h.auto_b_proc = 4'd5;
        timing_state_h.auto_c_proc = 4'd10;
        timing_state_h.next_out_val = 4'd0; 
        if (!reset_n) begin
            reg_state_val <= 4'd0;
            timing_state_h.auto_b_proc <= 4'd5; 
            timing_state_h.auto_c_proc <= 4'd10; 
            timing_state_h.next_out_val <= 4'd0; 
        end else begin
            fork : my_timing_fork
                automatic int count_fork_init = 0;
                @(posedge clk);
                timing_state_h.auto_b_proc <= captured_in_val;
                count_fork_init = count_fork_init + 1;
                timing_state_h.auto_c_proc <= timing_state_h.auto_c_proc + count_fork_init; 
                timing_state_h.next_out_val <= timing_state_h.auto_b_proc + timing_state_h.auto_c_proc; 
            join_none
            reg_state_val <= reg_state_val + 1;
        end
        out_val <= timing_state_h.next_out_val;
    end
endmodule
module ForkClassHandle (
    input bit enable_in,
    input logic [7:0] data_in,
    output logic [7:0] result_out
);
    class MyData;
        logic [7:0] value;
        function new();
            this.value = 8'd0;
        endfunction
        function void set_value(logic [7:0] v);
            this.value = v;
        endfunction
    endclass
    class MyParentState;
        logic [7:0] parent_scope_var;
    endclass
    MyData my_handle;
    always_comb begin : class_proc_block
        my_handle = null;
        result_out = 8'd0;
        automatic MyParentState parent_state_h = new();
        parent_state_h.parent_scope_var = 8'd1;
        if (enable_in) begin
            my_handle = new();
            my_handle.set_value(data_in);
            fork : class_fork
                automatic logic [7:0] fork_local_var = 8'd5;
                parent_state_h.parent_scope_var = parent_state_h.parent_scope_var + 2;
                my_handle.value = my_handle.value + fork_local_var;
                result_out = my_handle.value + parent_state_h.parent_scope_var;
            join_none
        end else begin
        end
    end
endmodule
module NestedForks (
    input logic [1:0] selector,
    output logic [7:0] sum_out
);
    class MyNestedState;
        logic [7:0] var_a_proc;
        logic [7:0] var_b_proc;
        logic [7:0] outer_local_var;
        logic [7:0] temp_sum_out;
    endclass
    always_comb begin : outer_proc
        automatic MyNestedState nested_state_h = new();
        nested_state_h.var_a_proc = 8'd10;
        nested_state_h.var_b_proc = 8'd20;
        nested_state_h.outer_local_var = 8'd1;
        nested_state_h.temp_sum_out = 8'd0;
        fork : outer_fork_jn
            automatic logic [7:0] outer_fork_var = 8'd2;
            nested_state_h.var_a_proc = nested_state_h.var_a_proc + 1;
            nested_state_h.outer_local_var = nested_state_h.outer_local_var + 1;
            case (selector)
                2'b00: begin : inner_block_a
                    automatic logic [7:0] inner_block_var = 8'd3;
                    nested_state_h.var_b_proc = nested_state_h.var_b_proc + 1;
                    nested_state_h.temp_sum_out = nested_state_h.var_a_proc + nested_state_h.var_b_proc + outer_fork_var + inner_block_var + nested_state_h.outer_local_var;
                end
                2'b01: fork : inner_fork_jn
                    automatic logic [7:0] inner_fork_var = 8'd4;
                    nested_state_h.var_b_proc = nested_state_h.var_b_proc + 2;
                    inner_fork_var = inner_fork_var + 1;
                    outer_fork_var = outer_fork_var + 1;
                    nested_state_h.temp_sum_out = nested_state_h.var_a_proc + nested_state_h.var_b_proc + outer_fork_var + inner_fork_var + nested_state_h.outer_local_var;
                join_none
                default: nested_state_h.temp_sum_out = 8'hFF;
            endcase
        join_none
        sum_out = nested_state_h.temp_sum_out;
    end
endmodule
module ForkJoinAny (
    input bit start_trigger,
    output logic [7:0] done_flag
);
    class MyJoinAnyState;
        logic [7:0] common_val_proc;
    endclass
    always_comb begin : join_any_proc
        automatic MyJoinAnyState join_any_state_h = new();
        logic [7:0] temp_done_flag = 8'd0;
        join_any_state_h.common_val_proc = 8'd0;
        if (start_trigger) begin
            fork : my_join_any_fork
                automatic logic [7:0] thread1_val = 8'd10;
                join_any_state_h.common_val_proc = join_any_state_h.common_val_proc + thread1_val;
            join_any
            temp_done_flag = 8'd1;
        end
        done_flag = temp_done_flag;
    end
endmodule
module TaskWithForkAndDelay (
    input bit clk_in,
    input logic [7:0] input_data,
    output logic [7:0] output_result
);
    logic [7:0] shared_mem;
    task my_forking_task(input logic [7:0] task_in, output logic [7:0] task_out);
        automatic logic [7:0] task_local_var = task_in;
        fork : internal_task_fork
            automatic logic [7:0] fork_var = 8'd1;
            task_local_var = task_local_var + fork_var;
            shared_mem <= task_local_var; 
        join_none
        task_out <= task_local_var; 
    endtask
    function automatic logic [7:0] my_blocking_func(input logic [7:0] func_in);
        automatic logic [7:0] func_local = func_in;
        func_local = func_local + 1;
        return func_local;
    endfunction
    always_ff @(posedge clk_in) begin : main_process_task_func
        my_forking_task(input_data, output_result);
        shared_mem <= my_blocking_func(shared_mem);
    end
endmodule
module BlockWithFork (
    input logic [3:0] in_val_block,
    output logic [3:0] out_val_block
);
    class MyBlockState;
        logic [3:0] block_var_a_proc;
        logic [3:0] block_var_b_proc;
        logic [3:0] inner_block_var;
        logic [3:0] temp_val_for_output;
    endclass
    always_comb begin : named_main_block
        automatic MyBlockState block_state_h = new();
        block_state_h.block_var_a_proc = 4'd1;
        block_state_h.block_var_b_proc = 4'd2;
        block_state_h.inner_block_var = 4'd3;
        block_state_h.temp_val_for_output = 4'd0;
        fork : block_internal_fork
            block_state_h.block_var_a_proc = block_state_h.block_var_a_proc + 1;
            block_state_h.block_var_b_proc = block_state_h.block_var_b_proc + 2;
            block_state_h.inner_block_var = block_state_h.inner_block_var + 1;
            block_state_h.temp_val_for_output = block_state_h.block_var_a_proc + block_state_h.block_var_b_proc + block_state_h.inner_block_var + in_val_block;
        join_none
        out_val_block = block_state_h.temp_val_for_output + 1;
    end
endmodule
