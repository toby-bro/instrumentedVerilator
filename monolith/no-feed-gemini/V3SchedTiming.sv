module SchedSensitivityLists (
    input logic clk_i,
    input logic rst_ni,
    input logic en_i,
    input logic data_in_i,
    output logic [7:0] data_out_o,
    output logic busy_o,
    output logic [3:0] counter_o
);
    logic [7:0] reg_q;
    logic [3:0] count_r;
    logic       state_ff;
    event       event_go;
    event       event_done;
    always_ff @(posedge clk_i or negedge rst_ni) begin : block_ff_logic
        if (!rst_ni) begin
            reg_q <= 8'h00;
            state_ff <= 1'b0;
        end else begin
            reg_q <= {reg_q[6:0], data_in_i};
            state_ff <= en_i;
            if (en_i) begin
                -> event_go;
            end
        end
    end
    always_comb begin : block_comb_logic
        busy_o = state_ff;
        data_out_o = reg_q;
    end
    always @(event_go or event_done or clk_i) begin : block_event_wait
        if (event_go.triggered) begin
            count_r = 4'h0;
            wait (data_out_o[0] == 1'b1);
            count_r = count_r + 1;
            -> event_done;
        end else if (event_done.triggered) begin
            count_r = 4'hF;
        end else if (clk_i.posedge) begin
            if (count_r != 4'hF) begin
                count_r = count_r + 1;
            end
        end
    end
    assign counter_o = count_r;
endmodule
module SchedForkAwaitProcesses (
    input logic start_i,
    input logic [7:0] config_i,
    output logic result_o,
    output logic [15:0] total_count_o
);
    logic proc_started;
    logic [15:0] local_total_count;
    event trigger_fork_done;
    event trigger_subtask_done;
    always_ff @(posedge start_i) begin : main_process_block
        automatic logic [7:0] task_id; 
        automatic logic [7:0] intermediate_val; 
        proc_started = 1'b1; 
        local_total_count = 16'h0; 
        fork : my_fork_tasks
            begin : subtask_a 
                task_id = 8'hA;
                intermediate_val = config_i + 8'h1;
                wait (intermediate_val > 8'h0); 
                local_total_count += task_id;
                -> trigger_subtask_done;
            end
            begin : subtask_b 
                task_id = 8'hB;
                intermediate_val = config_i * 8'h2;
                wait (trigger_subtask_done.triggered); 
                local_total_count += task_id;
            end
            begin : subtask_c
                task_id = 8'hC;
                local_total_count += task_id;
            end
        join_none
        wait (proc_started == 1'b1); 
        fork : my_fork_join_any
            begin : subtask_d
                automatic logic temp_val;
                temp_val = config_i % 8'h3;
                if (temp_val == 0) wait (1'b1); 
                local_total_count += 8'hD;
            end
            begin : subtask_e
                local_total_count += 8'hE;
            end
        join_any
        result_o = (local_total_count > 16'h0) ? 1'b1 : 1'b0;
        -> trigger_fork_done;
    end
    assign total_count_o = local_total_count;
endmodule
module SchedClassCoroutines (
    input logic clk_i,
    input logic enable_i,
    input int   input_val_i,
    output int  output_val_o,
    output logic class_done_o
);
    class MyScheduler {
        int internal_state;
        int accumulated_sum;
        logic active;
        event operation_complete;
        function new();
            internal_state = 0;
            accumulated_sum = 0;
            active = 1'b0;
        endfunction
        function automatic void process_data(input int val);
            int temp_var;
            active = 1'b1;
            temp_var = val * 2;
            this.internal_state = temp_var; 
            wait (this.internal_state > 0); 
            fork : class_task_fork
                automatic int fork_local_var; 
                begin : sub_op_a
                    fork_local_var = this.internal_state + 1;
                    accumulated_sum += fork_local_var;
                end
                begin : sub_op_b
                    fork_local_var = val - 1;
                    if (fork_local_var > 0) begin
                        wait (accumulated_sum > 10); 
                        accumulated_sum += fork_local_var;
                    end
                end
            join_any
            active = 1'b0;
            -> operation_complete;
        endfunction
        function int get_result();
            return accumulated_sum;
        endfunction
        function logic is_active();
            return active;
        endfunction
    endclass
    MyScheduler scheduler_inst;
    always_ff @(posedge clk_i) begin : scheduler_instantiation_block
        if (scheduler_inst == null) begin
            scheduler_inst = new(); 
        end
    end
    always_comb begin : scheduler_logic_block
        if (enable_i && scheduler_inst != null && !scheduler_inst.is_active()) begin
            scheduler_inst.process_data(input_val_i); 
        end
        current_output_val = (scheduler_inst != null) ? scheduler_inst.get_result() : 0;
        class_done_o = (scheduler_inst != null) ? !scheduler_inst.is_active() : 1'b0;
    end
    assign output_val_o = current_output_val;
endmodule
