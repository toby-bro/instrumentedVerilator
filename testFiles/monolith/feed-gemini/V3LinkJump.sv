module LoopJumpTest (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic [7:0] in_c,
    output logic [7:0] out_val
);
    logic [7:0] local_val = 8'd0;
    logic [7:0] i, j, k;
    integer arr [4];
    always_comb begin : outer_block
        local_val = 8'd0;
        repeat (in_a + 1) begin : repeat_loop_block
            automatic int loop_var_a = 0;
            local_val += 8'd1;
            if (local_val == in_b) begin
                break;
            end
            if (local_val == in_c) begin
                continue;
            end
            loop_var_a++;
        end
        for (i = 0; i < in_a; i = i + 1) begin : for_loop_block
            if (i == in_b) begin
                break;
            end
            if (i == in_c) begin
                continue;
            end
            local_val += 8'd2;
        end
        j = 0;
        while (j < in_b) begin : while_loop_block
            automatic int loop_var_b = 0;
            j++;
            if (j == in_c) begin
                break;
            end
            local_val += 8'd3;
            loop_var_b++;
        end
        k = 0;
        do begin : do_while_loop_block
            automatic int loop_var_c = 0;
            k++;
            if (k == in_b) begin
                continue;
            end
            local_val += 8'd4;
            loop_var_c++;
        end while (k < in_a);
        foreach (arr[i]) begin : foreach_loop_block
            automatic int loop_var_d = 0;
            arr[i] = i;
            if (i == in_b[1:0]) begin
                break;
            end
            if (i == in_c[1:0]) begin
                continue;
            end
            local_val += 8'd5;
            loop_var_d++;
        end
    end
    assign out_val = local_val;
endmodule
module FunctionReturnTest (
    input logic [7:0] in_data,
    input logic [7:0] in_limit,
    input logic clk,
    output logic [7:0] out_result
);
    function automatic logic [7:0] my_function_val (logic [7:0] value);
        logic [7:0] temp_val = value;
        if (temp_val > in_limit) begin
            return temp_val;
        end
        return temp_val + 1;
    endfunction
    function automatic void my_function_no_ret_val (logic [7:0] value);
        logic [7:0] temp_val = value;
        if (temp_val > in_limit) begin
            return;
        end
    endfunction
    function automatic logic [7:0] my_function_missing_ret_val (logic [7:0] value);
        if (value > 5) begin
            return 0;
        end
        return value;
    endfunction
    task automatic my_task_no_ret (input logic [7:0] val_in, output logic [7:0] val_out);
        val_out = val_in + 1;
        if (val_out > in_limit) begin
            return;
        end
    endtask
    task automatic my_task_with_ret_val_fixed (input logic [7:0] val_in, output logic [7:0] val_out);
        val_out = val_in + 2;
        if (val_out > in_limit) begin
            return;
        end
    endtask
    function logic [7:0] func_in_fork (logic [7:0] value);
        if (value == 0) begin
            return value;
        end
        return value + 1;
    endfunction
    logic [7:0] func_val_res;
    logic [7:0] task_no_ret_res;
    logic [7:0] task_with_ret_res_dummy;
    logic [7:0] func_no_ret_val_res_dummy;
    logic [7:0] func_missing_ret_val_res;
    always_ff @(posedge clk) begin : main_logic
        func_val_res = my_function_val(in_data);
        my_function_no_ret_val(in_data);
        func_missing_ret_val_res = my_function_missing_ret_val(in_data);
        my_task_no_ret(in_data, task_no_ret_res);
        my_task_with_ret_val_fixed(in_data, task_with_ret_res_dummy);
        fork : return_in_fork_test
            func_in_fork(in_data);
        join_none
        out_result = func_val_res + task_no_ret_res + func_missing_ret_val_res;
    end
endmodule
module DisableForkTest (
    input logic [7:0] in_enable,
    input logic [7:0] in_val,
    input logic clk,
    output logic [7:0] out_state
);
    logic [7:0] state = 8'd0;
    logic [7:0] comb_val_for_sibling_block;
    task automatic my_dummy_task();
        state = 8'd99;
    endtask
    always_comb begin : some_sibling_block
        comb_val_for_sibling_block = 8'd100;
    end
    always_ff @(posedge clk) begin : main_block
        state = 8'd1;
        if (in_enable == 1) begin
            disable my_dummy_task;
        end
        fork : my_outer_fork
            begin : block_in_fork1
                automatic int fork_var_1 = 1;
                state = 8'd2 + fork_var_1;
                if (in_enable == 2) begin
                    disable fork;
                end
            end
            begin : block_in_fork2
                state = 8'd3;
                if (in_enable == 3) begin
                    disable block_in_fork1;
                end
            end
        join_none
        if (in_enable == 4) begin : nested_block
            if (in_val == 1) begin : target_block_ancestor
                state = 8'd4;
                if (in_enable == 5) begin
                    disable main_block;
                end
            end
        end
        if (in_enable == 6) begin : block_containing_fork_test
            fork : inner_fork_for_disable_test
                state = 8'd5;
            join_none
            if (in_enable == 7) begin
                disable block_containing_fork_test;
            end
        end
        if (in_enable == 8) begin
            disable some_sibling_block;
        end
        fork : self_disable_fork
            begin : fork_internal_block
                if (in_enable == 9) begin
                    disable self_disable_fork;
                end
            end
        join_none
        for (int x = 0; x < in_val; x++) begin : some_loop_disabled_unroll
            state++;
        end
    end
    assign out_state = state;
endmodule
