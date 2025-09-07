module RepeatLoopModule (
    input logic clk,
    input logic reset_n,
    input int in_data,
    output int out_sum
);
    logic [7:0] repeat_counter_q;
    int sum_local_q;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            repeat_counter_q = 8'd0;
            sum_local_q = 0;
            out_sum = 0;
        end else begin
            sum_local_q = 0;
            repeat (in_data % 10 + 1) begin : REPEAT_BLOCK
                sum_local_q = sum_local_q + 1;
                begin : INNER_REPEAT_BLOCK
                    repeat_counter_q = repeat_counter_q + 1;
                end
            end
            out_sum = sum_local_q + repeat_counter_q;
        end
    end
endmodule
module DoWhileLoopModule (
    input logic clk,
    input logic reset_n,
    input int max_val,
    output int final_count
);
    int count_q;
    int inner_count_q;
    logic done_flag_q;
    int current_final_count_q;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            count_q = 0;
            inner_count_q = 0;
            current_final_count_q = 0;
            final_count = 0;
            done_flag_q = 1'b0;
        end else begin
            count_q = 0;
            inner_count_q = 0;
            current_final_count_q = 0;
            done_flag_q = 1'b0;
            do begin : DO_WHILE_LOOP_BLOCK
                count_q = count_q + 1;
                if (count_q > max_val) begin
                    done_flag_q = 1'b1;
                    break;
                end
                inner_count_q = 0;
                while (inner_count_q < 5) begin : INNER_WHILE_BLOCK
                    inner_count_q = inner_count_q + 1;
                    if (inner_count_q == 3) begin
                        continue;
                    end
                    current_final_count_q = current_final_count_q + 1;
                end
            end while (count_q <= max_val && !done_flag_q);
            final_count = current_final_count_q + count_q;
        end
    end
endmodule
module FunctionTaskReturnModule (
    input int in_a,
    input int in_b,
    input logic select_func,
    output int out_result
);
    int internal_result_reg;
    function automatic int my_function (input int val1, input int val2);
        if (val1 > val2) begin
            return val1 + val2;
        end else begin
            return val1 - val2;
        end
    endfunction
    task automatic my_task (input int val_in, output int val_out);
        val_out = val_in * 2;
        if (val_in < 0) begin
            return;
        end
        val_out = val_out + 1;
    endtask
    always_comb begin
        internal_result_reg = 0;
        if (select_func) begin
            internal_result_reg = my_function(in_a, in_b);
        end else begin
            my_task(in_a, internal_result_reg);
        end
        out_result = internal_result_reg;
    end
endmodule
module LoopControlModule (
    input logic clk,
    input logic reset_n,
    input int array_data [4],
    input int loop_limit,
    output int sum_output
);
    int i_q;
    int j_q;
    int temp_sum_q;
    int current_val_q;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            temp_sum_q = 0;
            sum_output = 0;
        end else begin
            temp_sum_q = 0;
            i_q = 0;
            while (i_q < loop_limit && i_q < 10) begin : WHILE_LOOP
                i_q = i_q + 1;
                if (i_q % 2 == 0) begin
                    continue;
                end
                temp_sum_q = temp_sum_q + i_q;
                if (temp_sum_q > 20) begin
                    break;
                end
            end
            foreach (array_data[j_q]) begin : FOREACH_LOOP
                current_val_q = array_data[j_q];
                if (current_val_q == 0) begin
                    continue;
                end
                temp_sum_q = temp_sum_q + current_val_q;
                if (temp_sum_q > 100) begin
                    break;
                end
            end
            sum_output = temp_sum_q;
        end
    end
endmodule
module NamedBlockDisableModule (
    input int in_val,
    input logic disable_enable,
    output int result_out
);
    int val1_q, val2_q, val3_q;
    always_comb begin : MAIN_BLOCK
        val1_q = in_val;
        val2_q = 0;
        val3_q = 0;
        begin : OUTER_BLOCK
            val1_q = val1_q * 2;
            val2_q = val1_q + 5;
            begin : INNER_BLOCK
                val3_q = val2_q * 3;
                if (in_val > 10 && disable_enable) begin
                    disable OUTER_BLOCK;
                end
                val3_q = val3_q + 1;
            end
            val2_q = val3_q - 2;
        end
        result_out = val1_q + val2_q + val3_q;
    end
endmodule
module ForkJoinDisableModule (
    input logic clk,
    input logic reset_n,
    input int ctrl_val,
    input logic disable_entire_fork,
    input logic disable_fork_branch1,
    output int final_sum
);
    int sum_fork_result_q;
    int branch1_val_q, branch2_val_q;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            sum_fork_result_q = 0;
            branch1_val_q = 0;
            branch2_val_q = 0;
            final_sum = 0;
        end else begin
            sum_fork_result_q = 0;
            branch1_val_q = 0;
            branch2_val_q = 0;
            FORK_MAIN: fork
                begin : FORK_BRANCH_1
                    int local_var1 = ctrl_val;
                    if (local_var1 > 5) begin
                        local_var1 = local_var1 * 2;
                    end
                    branch1_val_q = local_var1;
                end
                begin : FORK_BRANCH_2
                    int local_var2 = ctrl_val + 1;
                    if (local_var2 < 0) begin
                        local_var2 = local_var2 - 5;
                    end
                    branch2_val_q = local_var2;
                end
            join_any
            if (disable_entire_fork) begin
                disable FORK_MAIN;
            end
            if (disable_fork_branch1) begin
                disable FORK_BRANCH_1;
            end
            sum_fork_result_q = branch1_val_q + branch2_val_q;
            final_sum = sum_fork_result_q;
        end
    end
endmodule
