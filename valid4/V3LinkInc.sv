module BasicIncDec (
    input logic [7:0] in_val_a,
    input logic [7:0] in_val_b,
    input logic       in_sel,
    output logic [7:0] out_result_a,
    output logic [7:0] out_result_b
);
    logic [7:0] var_a, var_b, temp_a, temp_b;
    logic [7:0] loop_counter;
    logic [7:0] case_sel_val;
    logic [7:0] case_item_var;
    logic [7:0] current_case_item_val;
    logic       case_item_match_flag;
    always_comb begin
        var_a = in_val_a;
        var_b = in_val_b;
        loop_counter = 0;
        temp_a = 0;
        temp_b = 0;
        case_sel_val = in_val_a % 3;
        case_item_var = in_val_b;
        temp_a = var_a++;
        var_b--;
        temp_b = --var_b;
        ++var_a;
        if (in_sel) begin
            temp_a += var_a++;
            temp_b -= --var_b;
        end else begin
            var_a--;
            ++var_b;
        end
        while (loop_counter < 5) begin
            temp_a += loop_counter;
            temp_b -= loop_counter;
            loop_counter++;
            var_a++;
            var_b--;
        end
        for (logic [3:0] i = 0; i < 3; i++) begin
            if (i == 1) begin
                var_a++;
            end
        end
        current_case_item_val = case_item_var;
        case_item_match_flag = 1'b0;
        case (case_sel_val)
            0: begin
                var_a++;
                temp_a = var_a;
            end
            current_case_item_val: begin
                temp_b = var_b--;
                case_item_match_flag = 1'b1;
            end
            2: begin
                temp_a = ++var_a;
                temp_b = --var_b;
            end
            default: begin
                var_a = var_a + 1;
            end
        endcase
        if (case_item_match_flag) begin
            case_item_var++;
        end
        out_result_a = temp_a + var_a;
        out_result_b = temp_b + var_b;
    end
endmodule
module ArrayIncDec (
    input logic [7:0] in_idx_base,
    input logic [7:0] in_array_val,
    input logic       in_flag_a,
    input logic       in_flag_b,
    output logic [7:0] out_sum_array,
    output logic [7:0] out_idx_final
);
    logic [7:0] my_array [0:9];
    logic [3:0] index_var;
    logic [7:0] sum_local;
    logic       cond_result;
    logic [7:0] foreach_sum;
    logic [7:0] log_eq_val_a;
    logic [7:0] log_eq_val_b;
    logic       log_eq_result;
    logic [7:0] log_if_cond_val;
    logic [7:0] log_if_result;
    logic [7:0] temp_log_if_val;
    logic [3:0] sfx_val_for_idx_func = 0;
    function automatic logic [3:0] get_sfx_idx_with_inc();
        logic [3:0] temp_sfx;
        temp_sfx = sfx_val_for_idx_func;
        sfx_val_for_idx_func++;
        get_sfx_idx_with_inc = temp_sfx;
    endfunction
    always_comb begin
        sum_local = 0;
        foreach_sum = 0;
        index_var = in_idx_base % 10;
        sfx_val_for_idx_func = in_idx_base % 10;
        for (int i = 0; i < 10; i++) begin
            my_array[i] = in_array_val + i;
        end
        my_array[get_sfx_idx_with_inc()]++;
        log_eq_val_a = in_idx_base;
        log_eq_val_b = in_array_val;
        log_eq_result = (log_eq_val_a == log_eq_val_b);
        log_if_cond_val = log_eq_val_a;
        temp_log_if_val = log_if_cond_val;
        if (log_if_cond_val > 5) begin
            log_if_result = temp_log_if_val;
            temp_log_if_val++;
        end else begin
            --temp_log_if_val;
            log_if_result = temp_log_if_val;
        end
        cond_result = (in_flag_a && log_eq_result) || (in_flag_b && (log_if_result > 0));
        if (cond_result) begin
            my_array[index_var % 10]--;
        end
        foreach (my_array[idx]) begin
            foreach_sum += my_array[idx]++;
        end
        fork : jump_block_a
            logic [7:0] fork_var_a;
            fork_var_a = in_array_val;
            fork_var_a++;
            sum_local += fork_var_a;
        join_none
        fork : jump_block_b
            logic [7:0] fork_var_b;
            fork_var_b = in_array_val;
            --fork_var_b;
            sum_local += fork_var_b;
        join_none
        for (int i = 0; i < 10; i++) begin
            sum_local += my_array[i];
        end
        out_sum_array = sum_local + foreach_sum;
        out_idx_final = index_var + sfx_val_for_idx_func;
    end
endmodule
module FunctionAndClassIncDec (
    input logic [15:0] in_value,
    input logic        in_enable_task,
    output logic [15:0] out_processed_val,
    output logic [7:0] out_counter_val
);
    logic [7:0] func_counter;
    logic [7:0] task_counter;
    logic [15:0] temp_val;
    class MyClass;
        rand int val;
        function new(int v);
            val = v;
        endfunction
        function int get_val();
            return val++;
        endfunction
        function int dec_val();
            return --val;
        endfunction
    endclass
    function automatic logic [7:0] process_func(logic [7:0] start_val);
        logic [7:0] f_temp;
        f_temp = start_val;
        f_temp++;
        process_func = ++f_temp;
    endfunction
    task automatic process_task(input logic [7:0] start_val);
        logic [7:0] t_temp;
        t_temp = start_val;
        t_temp--;
        task_counter = t_temp--;
    endtask
    always_comb begin
        MyClass my_object_inst;
        func_counter = 0;
        task_counter = 0;
        temp_val = in_value;
        my_object_inst = new(in_value);
        func_counter = process_func(in_value[7:0]);
        temp_val = my_object_inst.get_val();
        temp_val += my_object_inst.dec_val();
        if (in_enable_task) begin
            process_task(in_value[7:0]);
        end else begin
            task_counter = 0;
        end
        out_processed_val = temp_val;
        out_counter_val = func_counter + task_counter;
    end
endmodule
module ComplexControlFlowIncDec (
    input logic [3:0] in_gen_count,
    input logic [7:0] in_start_val,
    output logic [7:0] out_final_val
);
    logic [7:0] current_val;
    logic [7:0] fork_join_sum;
    always_comb begin
        current_val = in_start_val;
        fork_join_sum = 0;
        begin
            logic [7:0] fork_val_a_local = current_val;
            logic [7:0] branch_a_sum_val = fork_val_a_local++;
            logic [7:0] fork_val_b_local = current_val;
            logic [7:0] branch_b_sum_val = --fork_val_b_local;
            fork_join_sum = branch_a_sum_val + branch_b_sum_val;
        end
        current_val = fork_join_sum;
    end
    logic [7:0] gen_output_arr [0:9];
    genvar gi;
    for (gi = 0; gi < 10; gi++) begin : gen_calc
        always_comb begin
            if (gi < in_gen_count) begin
                logic [7:0] temp_gen_val = in_start_val + gi;
                if (gi % 2 == 0) begin
                    gen_output_arr[gi] = temp_gen_val++;
                end else begin
                    gen_output_arr[gi] = --temp_gen_val;
                end
            end else begin
                gen_output_arr[gi] = 0;
            end
        end
    end
    always_comb begin
        logic [7:0] final_sum = 0;
        for (int i = 0; i < in_gen_count; i++) begin
            final_sum += gen_output_arr[i];
        end
        out_final_val = current_val + final_sum;
    end
endmodule
