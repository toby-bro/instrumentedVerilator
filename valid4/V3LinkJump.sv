module ModuleLoops (
    input logic [7:0] in_data,
    input logic       in_en,
    output logic [7:0] out_result
);
    logic [7:0] temp_val;
    logic [3:0] counter;
    logic       done_flag;
    logic [7:0] do_while_out_val_ff;
    (* verilator_full_unroll *)
    always_comb begin : named_loop_block_full
        temp_val = in_data; 
        counter = 0;        
        if (in_en) begin
            repeat (5) begin : repeat_loop_body
                counter = counter + 1;
                if (counter == 3) begin
                    continue;
                end
                if (counter == 6) begin
                    break;
                end
                temp_val = temp_val + counter;
            end
            for (int k = 0; k < 4; k++) begin : for_loop_body
                temp_val = temp_val - k;
                if (k == 1) continue;
                if (k == 3) break;
            end
        end else begin
            counter = 0;
        end
    end
    logic [7:0] current_val_reg; 
    (* verilator_no_unroll *)
    always_ff @(posedge in_en) begin : named_loop_block_disable
        int i = 0;
        current_val_reg <= 0; 
        do begin : do_while_body
            logic [7:0] inner_do_while_var = 0; 
            current_val_reg <= current_val_reg + 1 + inner_do_while_var;
            if (current_val_reg > 10) begin
                break;
            end
            i++;
            if (i % 2 == 0) continue;
        end while (current_val_reg < 20);
        do_while_out_val_ff <= current_val_reg; 
    end
    logic [3:0] array_data [4];
    logic       foreach_sum_out_flag;
    always_comb begin
        int sum = 0;
        array_data = '{1, 2, 3, 4};
        foreach (array_data[idx]) begin
            sum += array_data[idx];
            if (idx == 2) break;
        end
        foreach_sum_out_flag = (sum > 0);
    end
    class MySimpleClass;
        int member_var;
        function new(int val);
            member_var = val;
        endfunction
    endclass
    MySimpleClass instance_a;
    always_comb begin
        done_flag = 0; 
        if (in_en) begin
            instance_a = new(in_data); 
            done_flag = (instance_a.member_var > 10);
        end else begin
            instance_a = null; 
            done_flag = 0;
        end
    end
    assign out_result = temp_val + (done_flag ? 1 : 0) + (foreach_sum_out_flag ? 1 : 0) + do_while_out_val_ff;
endmodule
module ModuleFuncTaskReturn (
    input logic [7:0] func_in,
    input logic [7:0] task_in,
    output logic [7:0] func_out,
    output logic [7:0] task_out,
    output logic       dummy_flag
);
    logic [7:0] func_internal_val;
    logic [7:0] task_internal_val;
    function automatic logic [7:0] calc_func(logic [7:0] val);
        logic [7:0] local_calc;
        local_calc = val * 2;
        if (val > 10) begin
            return local_calc + 1;
        end else begin
            return local_calc;
        end
    endfunction
    task automatic modify_task(input logic [7:0] val, output logic [7:0] result);
        logic [7:0] temp_task_var;
        temp_task_var = val + 5;
        if (temp_task_var > 100) begin
            return; 
        end
        result = temp_task_var;
    endtask
    task automatic illegal_return_task();
        fork begin : fork_block_illegal_return
            logic [7:0] dummy_var_in_fork = 0; 
            dummy_var_in_fork = dummy_var_in_fork + 1;
        end join_any
    endtask
    always_comb begin
        func_internal_val = calc_func(func_in);
        func_out = func_internal_val;
        task_internal_val = 0; 
        modify_task(task_in, task_internal_val);
        task_out = task_internal_val;
        illegal_return_task();
        dummy_flag = (func_internal_val > task_internal_val);
    end
    class DummyClass;
        int data;
        function new();
            data = 0;
        endfunction
    endclass
    DummyClass dc_inst;
    always_ff @(posedge func_in[0]) begin
        dc_inst <= new(); 
        if (func_in[0]) begin
            if (dc_inst != null) begin 
                dc_inst.data <= func_in[7]; 
            end
        end
    end
endmodule
module ModuleDisableBlocks (
    input logic [2:0] control_sig,
    input logic [7:0] data_in,
    input logic       clk, 
    output logic [7:0] data_out
);
    logic [7:0] result_from_comb_blocks;
    logic [7:0] result_from_fork_block;
    always_comb begin
        logic [7:0] current_val;
        current_val = data_in; 
        begin : my_named_block
            logic [7:0] block_local_var = 0; 
            current_val = current_val + block_local_var;
            if (control_sig == 3'b001) begin
                disable my_named_block; 
            end
            current_val = current_val + 1; 
        end
        begin : another_named_block
            logic [7:0] another_local_var = 0; 
            current_val = current_val + another_local_var;
            if (control_sig == 3'b100) begin
                disable another_named_block; 
            end
            current_val = current_val + 4; 
        end
        result_from_comb_blocks = current_val;
    end
    always_ff @(posedge clk) begin
        logic [7:0] fork_data_val;
        fork_data_val <= data_in; 
        begin : block_with_fork
            if (control_sig == 3'b010) begin
                disable block_with_fork; 
            end
            fork begin : child_fork_block
                int dummy_fork_var = 0; 
                dummy_fork_var = dummy_fork_var + 1; 
            end join_none 
            fork_data_val <= fork_data_val + 2; 
        end
        result_from_fork_block <= fork_data_val;
    end
    class AnotherClass;
        string name_str;
        function new(string s);
            name_str = s;
        endfunction
    endclass
    AnotherClass ac_inst;
    always_ff @(posedge clk) begin 
        ac_inst <= new("test"); 
        if (data_in[0]) begin
            if (ac_inst != null) begin 
                result_from_fork_block <= result_from_fork_block + ac_inst.name_str.len(); 
            end
        end
    end
    assign data_out = result_from_comb_blocks + result_from_fork_block;
endmodule
