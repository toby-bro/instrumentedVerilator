module BeginBlockHandling (
    input logic [7:0] in_data_h1,
    input bit enable_h1,
    output logic [7:0] out_data_h1
);
    logic [7:0] temp_val_h1;
    logic [7:0] block_var_a_h1;
    logic [7:0] inner_var_b_h1;
    logic [7:0] param_result_h1;
    always_comb begin : main_process_h1
        temp_val_h1 = in_data_h1 + 1;
        out_data_h1 = 8'h00;
        block_var_a_h1 = 0;
        inner_var_b_h1 = 0;
        param_result_h1 = 0;
        my_first_named_block: begin
            typedef struct packed {
                logic [3:0] f1;
                logic [3:0] f2;
            } my_block_struct_t_h1;
            my_block_struct_t_h1 block_struct_inst_h1;
            block_struct_inst_h1 = '{f1:0, f2:0};
            block_var_a_h1 = temp_val_h1 + 2;
            block_struct_inst_h1.f1 = block_var_a_h1[3:0];
            block_struct_inst_h1.f2 = block_var_a_h1[7:4];
            if (enable_h1) begin
                inner_var_b_h1 = block_var_a_h1 + 3;
                out_data_h1 = inner_var_b_h1;
            end else begin
                out_data_h1 = block_var_a_h1;
            end
        end
        another_block_h1: begin
            localparam int PARAM_VAL_h1 = 10;
            param_result_h1 = in_data_h1 + PARAM_VAL_h1;
            if (!enable_h1) begin
                out_data_h1 = param_result_h1;
            end
        end
    end
endmodule
module ForeachLoopExamples (
    input int array_in_l2[4],
    input int dyn_array_size_l2,
    input int queue_val_l2,
    input int assoc_key_l2,
    output int sum_out_l2,
    output int first_elem_out_l2
);
    int dynamic_array_l2[];
    int integer_queue_l2[$];
    int associative_array_l2[int];
    string test_string_l2 = "ForeachTest";
    int local_sum_l2;
    int first_element_l2;
    always_comb begin : foreach_process_l2
        local_sum_l2 = 0;
        first_element_l2 = 0;
        dynamic_array_l2 = new[0];
        integer_queue_l2 = {};
        foreach (array_in_l2[i_l2]) begin : fixed_array_loop_l2
            local_sum_l2 = local_sum_l2 + array_in_l2[i_l2];
            if (i_l2 == 0) first_element_l2 = array_in_l2[i_l2];
        end
        if (dyn_array_size_l2 > 0 && dyn_array_size_l2 < 5) begin
            dynamic_array_l2 = new[dyn_array_size_l2];
            for (int k_l2=0; k_l2<dyn_array_size_l2; k_l2++) dynamic_array_l2[k_l2] = k_l2 + 100;
            foreach (dynamic_array_l2[j_l2]) begin : dynamic_array_loop_l2
                local_sum_l2 = local_sum_l2 + dynamic_array_l2[j_l2];
            end
        end
        integer_queue_l2.push_back(queue_val_l2);
        integer_queue_l2.push_front(queue_val_l2 + 1);
        if (integer_queue_l2.size() > 0) begin
            integer_queue_l2.pop_front();
            foreach (integer_queue_l2[idx_q_l2]) begin : queue_loop_l2
                local_sum_l2 = local_sum_l2 + integer_queue_l2[idx_q_l2];
            end
        end
        associative_array_l2[assoc_key_l2] = assoc_key_l2 * 2;
        associative_array_l2[assoc_key_l2 + 1] = assoc_key_l2 * 3;
        if (associative_array_l2.num() > 0) begin
            foreach (associative_array_l2[key_var_l2]) begin : assoc_array_loop_l2
                local_sum_l2 = local_sum_l2 + associative_array_l2[key_var_l2];
            end
        end
        for (int char_idx_l2 = 0; char_idx_l2 < test_string_l2.len(); char_idx_l2++) begin : string_length_loop_l2
            local_sum_l2 = local_sum_l2 + char_idx_l2;
        end
        sum_out_l2 = local_sum_l2;
        first_elem_out_l2 = first_element_l2;
    end
endmodule
module FunctionTaskStaticVars (
    input int a_in_l3,
    input int b_in_l3,
    output int result_out_l3,
    output int static_read_out_l3
);
    int func_return_val_l3;
    int static_val_from_task_l3;
    function automatic int my_function_with_static(int val_l3);
        static int static_func_counter_l3 = 0;
        static_func_counter_l3 = static_func_counter_l3 + val_l3;
        return static_func_counter_l3;
    endfunction
    task automatic my_task_with_static(input int increment_l3);
        static int static_task_accum_l3 = 1000;
        static_task_accum_l3 = static_task_accum_l3 + increment_l3;
        static_val_from_task_l3 = static_task_accum_l3;
    endtask
    always_comb begin : static_var_process_l3
        function_task_wrapper: begin
            func_return_val_l3 = my_function_with_static(a_in_l3);
            my_task_with_static(b_in_l3);
            result_out_l3 = func_return_val_l3;
            static_read_out_l3 = static_val_from_task_l3;
        end
    end
endmodule
module ForkJoinAndIfDepth (
    input logic [2:0] control_l4,
    input bit condition1_l4,
    input bit condition2_l4,
    input bit condition3_l4,
    output logic [7:0] data_out_fork_l4,
    output logic [7:0] if_output_l4
);
    logic [7:0] fork_temp_a_l4, fork_temp_b_l4;
    logic [7:0] if_temp_val_l4;
    always_comb begin : fork_if_process_l4
        fork_temp_a_l4 = 0;
        fork_temp_b_l4 = 0;
        data_out_fork_l4 = 0;
        if_output_l4 = 0;
        if_temp_val_l4 = 0;
        fork : my_fork_block_l4
            if (control_l4[0]) begin : fork_branch_a_l4
                fork_temp_a_l4 = 8'hAA;
            end
            if (control_l4[1]) begin : fork_branch_b_l4
                fork_temp_b_l4 = 8'hBB;
            end
        join_any
        data_out_fork_l4 = fork_temp_a_l4 + fork_temp_b_l4;
        if (condition1_l4) begin : if_depth_1
            if_temp_val_l4 = 10;
            if (condition2_l4) begin : if_depth_2
                if_temp_val_l4 = if_temp_val_l4 + 20;
                if (condition3_l4) begin : if_depth_3
                    if_temp_val_l4 = if_temp_val_l4 + 30;
                end
            end
        end else begin : else_branch_depth_1
            if_temp_val_l4 = 5;
            if (!condition2_l4) begin : else_if_branch_depth_2
                if_temp_val_l4 = if_temp_val_l4 + 1;
            end
        end
        if_output_l4 = if_temp_val_l4;
    end
endmodule
module ClassAndScopeInteraction (
    input int class_input_val_l5,
    input bit use_class_l5,
    output int class_result_out_l5
);
    class MySimpleClass;
        int member_var;
        function new(int init_val);
            member_var = init_val;
        endfunction
        function int get_double();
            return member_var * 2;
        endfunction
    endclass
    MySimpleClass class_inst_handle_l5;
    always_comb begin : class_process_l5
        class_result_out_l5 = 0;
        class_instantiation_block: begin
            if (use_class_l5) begin
                class_inst_handle_l5 = new(class_input_val_l5);
                if (class_inst_handle_l5 != null) begin
                    class_result_out_l5 = class_inst_handle_l5.get_double();
                end
            end else begin
                class_inst_handle_l5 = new(class_input_val_l5 + 1);
                if (class_inst_handle_l5 != null) begin
                    class_result_out_l5 = class_inst_handle_l5.get_double() + 100;
                end
            end
        end
    end
endmodule
module CoverDeclExample (
    input logic [1:0] cover_in_l6,
    output logic [1:0] cover_out_l6
);
    covergroup my_cg_l6;
        coverpoint cover_in_l6 {
            bins zero = {0};
            bins one = {1};
            bins others = default;
        }
    endgroup
    always_comb begin : cover_process_l6
        cover_out_l6 = cover_in_l6;
    end
endmodule
