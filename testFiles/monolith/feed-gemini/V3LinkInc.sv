class MySimpleData;
    int value_m;
    function new(int init_val);
        this.value_m = init_val;
    endfunction
    function void increment();
        value_m++;
    endfunction
    function int get_val_pre_increment();
        return ++value_m;
    endfunction
    function int get_val_post_increment();
        return value_m++;
    endfunction
endclass
module SimpleIncDecProcessor (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic [7:0] out_val_a,
    output logic [7:0] out_val_b,
    output logic [7:0] out_expr_pre,
    output logic [7:0] out_expr_post
);
    logic [7:0] reg_a, reg_b;
    logic [7:0] temp_expr_val;
    always_comb begin
        MySimpleData my_data_obj;
        my_data_obj = new(in_a);
        reg_a = in_a;
        reg_b = in_b;
        temp_expr_val = 0;
        if (reg_a > 5) begin
            reg_a++;
        end else begin
            --reg_a;
        end
        my_data_obj.increment();
        temp_expr_val = my_data_obj.get_val_post_increment();
        out_expr_post = temp_expr_val;
        temp_expr_val = (++reg_b);
        out_expr_pre = temp_expr_val;
        reg_a = reg_b++;
        reg_b = reg_b--;
        out_val_a = reg_a;
        out_val_b = reg_b;
    end
endmodule
module LoopControlProcessor (
    input logic [3:0] in_limit,
    input logic [3:0] in_idx_start,
    output logic [7:0] out_sum_while,
    output logic [7:0] out_sum_for,
    output logic [7:0] out_sum_foreach
);
    logic [7:0] sum_w, sum_f, sum_fe;
    logic [3:0] current_idx;
    logic [7:0] data_arr [8];
    class LoopTracker;
        int count_l;
        function new(int initial_count);
            this.count_l = initial_count;
        endfunction
    endclass
    always_comb begin
        LoopTracker loop_obj;
        loop_obj = new(0);
        sum_w = 0;
        sum_f = 0;
        sum_fe = 0;
        current_idx = in_idx_start;
        for (int i=0; i<8; i++) begin
            data_arr[i] = i + 1;
        end
        while (loop_obj.count_l++ < in_limit) begin
            sum_w += loop_obj.count_l;
            if (loop_obj.count_l == 3) begin
                continue;
            end
            if (loop_obj.count_l == 5) begin
                break;
            end
            sum_w--;
        end
        for (int i=0; i < in_limit; i++) begin
            sum_f += i;
            if (i > 1) begin
                i++;
            end
        end
        foreach (data_arr[j]) begin
            sum_fe += data_arr[j];
            data_arr[j]++;
            current_idx++;
        end
        out_sum_while = sum_w;
        out_sum_for = sum_f;
        out_sum_foreach = sum_fe;
    end
endmodule
module FunctionTaskProcessor (
    input logic [7:0] in_f_val,
    input logic [7:0] in_t_val,
    output logic [7:0] out_func_ret,
    output logic [7:0] out_task_res
);
    logic [7:0] local_f_in, local_t_in;
    logic [7:0] func_res, task_res;
    class FTaskHelper;
        int func_counter;
        function new(int initial_val);
            this.func_counter = initial_val;
        endfunction
        function int get_and_dec();
            return func_counter--;
        endfunction
    endclass
    function automatic logic [7:0] calculate_func(logic [7:0] val_a);
        logic [7:0] temp_v;
        FTaskHelper ft_h_obj;
        ft_h_obj = new(val_a);
        temp_v = ft_h_obj.get_and_dec();
        temp_v += ++val_a;
        calculate_func = temp_v;
    endfunction
    task automatic process_task(input logic [7:0] val_x, output logic [7:0] val_y);
        logic [7:0] temp_k;
        temp_k = val_x;
        temp_k++;
        val_y = temp_k;
    endtask
    always_comb begin
        local_f_in = in_f_val;
        local_t_in = in_t_val;
        func_res = calculate_func(local_f_in);
        process_task(local_t_in, task_res);
        out_func_ret = func_res;
        out_task_res = task_res;
    end
endmodule
module ArraySelectProcessor (
    input logic [7:0] in_initial_val,
    input logic [3:0] in_test_idx,
    output logic [7:0] out_array_sum,
    output logic       out_comparison_res
);
    logic [7:0] my_dyn_arr [4];
    logic [3:0] dynamic_index_reg;
    logic [7:0] total_sum;
    class ArrayManipulator;
        int int_array[4];
        function new(int base);
            for(int i=0; i<4; i++) int_array[i] = base + i;
        endfunction
        function int get_element(int idx);
            return int_array[idx];
        endfunction
    endclass
    always_comb begin
        ArrayManipulator arr_manip;
        arr_manip = new(in_initial_val + 10);
        dynamic_index_reg = in_test_idx;
        total_sum = 0;
        out_comparison_res = 0;
        for (int i=0; i<4; i++) begin
            my_dyn_arr[i] = in_initial_val + i;
        end
        my_dyn_arr[dynamic_index_reg++]++;
        my_dyn_arr[++dynamic_index_reg]++;
        arr_manip.int_array[dynamic_index_reg--]++;
        if (my_dyn_arr[0] === (in_initial_val + 1)) begin
            out_comparison_res = 1;
        end else begin
            out_comparison_res = 0;
        end
        total_sum = (my_dyn_arr[1]++ > 15) ? my_dyn_arr[2] : my_dyn_arr[3];
        for (int i=0; i<4; i++) begin
            total_sum += my_dyn_arr[i];
            total_sum += arr_manip.get_element(i);
        end
        out_array_sum = total_sum;
    end
endmodule
module ConditionalLogicProcessor (
    input logic in_cond_val_a,
    input logic in_cond_val_b,
    input logic [1:0] in_case_sel,
    output logic [7:0] out_logic_total,
    output logic [7:0] out_case_total
);
    logic [7:0] current_x, current_y;
    logic [7:0] logic_sum;
    logic [7:0] case_sum_local;
    class CondHelper;
        int c_val;
        function new(int init);
            this.c_val = init;
        endfunction
        function bit evaluate_cond(bit flag);
            if (flag) c_val++;
            return (c_val == 10);
        endfunction
    endclass
    always_comb begin
        CondHelper cond_h_obj;
        cond_h_obj = new(5);
        current_x = 10;
        current_y = 20;
        logic_sum = 0;
        case_sum_local = 0;
        if ((current_x++ < 15) && (current_y-- > 15)) begin
            logic_sum += 1;
        end else begin
            logic_sum += 0;
        end
        if ((++current_x > 10) || (--current_y < 25)) begin
            logic_sum += 2;
        end else begin
            logic_sum += 0;
        end
        logic_sum += (in_cond_val_a ? current_x++ : current_y--);
        if (current_x === (++current_y - 1)) begin
            logic_sum += 4;
        end else begin
            logic_sum += 0;
        end
        if (cond_h_obj.evaluate_cond(in_cond_val_b)) begin
            logic_sum += 10;
        end
        case (in_case_sel)
            0: begin
                case_sum_local = current_x++;
            end
            1: begin
                case_sum_local = --current_y;
            end
            default: begin
                case_sum_local = current_x + current_y;
            end
        endcase
        out_logic_total = logic_sum;
        out_case_total = case_sum_local;
    end
endmodule
module GenForIncDec (
    input logic [3:0] gen_loop_base,
    output logic [7:0] gen_output_sum
);
    logic [7:0] sum_from_gen_blocks[2];
    logic [7:0] total_gen_sum;
    class GenBlockInfo;
        int id_val;
        function new(int id);
            this.id_val = id;
        endfunction
        function int get_processed_val(int input_v);
            input_v++;
            return input_v;
        endfunction
    endclass
    generate
        for (genvar g = 0; g < 2; g++) begin : gen_instance
            logic [7:0] local_val_g;
            always_comb begin
                GenBlockInfo gbi_obj;
                gbi_obj = new(g);
                local_val_g = gen_loop_base + gbi_obj.id_val;
                if (g == 0) begin
                    sum_from_gen_blocks[g] = gbi_obj.get_processed_val(local_val_g++);
                end else begin
                    sum_from_gen_blocks[g] = gbi_obj.get_processed_val(--local_val_g);
                end
            end
        end
    endgenerate
    always_comb begin
        total_gen_sum = 0;
        for (int i = 0; i < 2; i++) begin
            total_gen_sum += sum_from_gen_blocks[i];
        end
    end
    assign gen_output_sum = total_gen_sum;
endmodule
