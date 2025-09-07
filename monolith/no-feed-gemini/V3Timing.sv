module TimingFeatures_Delays (
    input logic clk_i,
    input logic reset_n_i,
    input logic [7:0] data_in_i,
    output logic [7:0] data_out_q,
    output logic toggle_q,
    output logic [7:0] delayed_assign_q
);
    logic internal_data_sync;
    logic internal_toggle_sync;
    assign #5 delayed_assign_q = data_in_i;
    always #10 internal_toggle_sync = ~internal_toggle_sync;
    assign toggle_q = internal_toggle_sync; 
    always @(posedge clk_i) begin
        if (!reset_n_i) begin
            data_out_q <= 8'b0;
        end else begin
            data_out_q[data_in_i[2:0] + 1'b1] <= #3 data_in_i;
        end
    end
    initial begin
        internal_toggle_sync = 1'b0;
        data_out_q = 8'b0;
        delayed_assign_q = 8'b0;
    end
endmodule
module TimingFeatures_Events (
    input logic clk_i,
    input logic reset_n_i,
    input logic enable_i,
    input logic [3:0] counter_val_i,
    output logic trigger_out_q,
    output logic wait_result_q
);
    logic [7:0] local_dynamic_var; 
    event my_named_event; 
    always @(posedge clk_i or negedge reset_n_i or enable_i) begin
        if (!reset_n_i) begin
            local_dynamic_var = 8'b0;
            trigger_out_q = 1'b0;
        end else begin
            local_dynamic_var = counter_val_i;
            trigger_out_q = ~trigger_out_q;
            -> my_named_event; 
        end
    end
    always @* begin
        wait_result_q = enable_i && (local_dynamic_var > 4'd5);
    end
    task automatic check_wait_and_event(input logic condition_in, output logic status_out);
        status_out = 1'b0;
        wait (condition_in && (local_dynamic_var < 8'hFF));
        status_out = 1'b1;
        @(my_named_event);
        status_out = 1'b0;
    endtask
    initial begin
        wait_result_q = 1'b0;
        check_wait_and_event(enable_i, wait_result_q);
        wait(1'b1); 
        wait(1'b0); 
    end
endmodule
module TimingFeatures_Forks (
    input logic start_i,
    input logic delay_val_i,
    output logic [2:0] fork_status_q
);
    task automatic dummy_suspendable_task();
        #1; 
    endtask
    task automatic process_control_task(input logic do_disable, output logic done_flag);
        done_flag = 1'b0;
        fork
            begin : child_proc
                dummy_suspendable_task(); 
                done_flag = 1'b1; 
            end
        join_none 
        if (do_disable) begin
            disable fork; 
        end
        wait fork; 
    endtask
    initial begin
        fork_status_q = 3'b000;
        if (start_i) begin
            fork
                begin : block_join_sync_1
                    #1; 
                    fork_status_q[0] = 1'b1;
                end
                begin : block_join_sync_2
                    #2;
                    fork_status_q[1] = 1'b1;
                end
            join
        end
        if (start_i) begin
            fork
                begin : block_join_any_sync_1
                    #1;
                    fork_status_q[2] = 1'b1;
                end
                begin : block_join_any_sync_2
                    #5;
                end
            join_any
        end
        if (start_i) begin
            fork
                begin : block_join_none_proc_1
                    #10;
                end
                begin : block_join_none_proc_2
                    #15;
                end
            join_none
        end
        process_control_task(1'b1, fork_status_q[0]); 
        process_control_task(1'b0, fork_status_q[1]); 
    end
endmodule
module TimingFeatures_ClassMethodsAndHierarchy (
    input logic clk_i,
    input logic data_in_i,
    output logic class_data_out_q
);
    class BaseClass;
        protected int internal_val_m = 0;
        virtual task automatic suspendable_base_task(input int increment);
            internal_val_m += increment;
            #1; 
            internal_val_m = internal_val_m * 2;
        endtask
        virtual function int get_val();
            return internal_val_m;
        endfunction
    endclass
    class DerivedClass extends BaseClass;
        virtual task automatic suspendable_base_task(input int increment); 
            internal_val_m += increment + 10;
            #2; 
            internal_val_m = internal_val_m * 3;
        endtask
        task automatic caller_task(input int initial_val);
            internal_val_m = initial_val;
            suspendable_base_task(1); 
        endtask
    endclass
    DerivedClass inst_derived;
    initial begin
        inst_derived = new(); 
        inst_derived.caller_task(10);
        class_data_out_q = inst_derived.get_val();
    end
    always @(posedge clk_i) begin
        class_data_out_q = data_in_i; 
    end
endmodule
module GeneralTiming_JumpBlockAndScopes (
    input logic clk_i,
    input logic cond_i,
    input logic [7:0] val_i,
    output logic [7:0] data_out_q
);
    logic [7:0] local_reg;
    always @(posedge clk_i) begin : main_proc_block
        data_out_q = 8'b0; 
        local_reg = val_i;
        if (cond_i) begin : jump_block_if
            #1;
            data_out_q = local_reg + 1;
        end else begin
            wait (val_i == 8'hFF);
            data_out_q = local_reg - 1;
        end
        for (int i=0; i<2; i++) begin : jump_block_for
            #1;
            data_out_q = data_out_q + 1;
        end
        case (val_i[1:0])
            2'b00: begin
                data_out_q = data_out_q; 
            end
            2'b01: begin
                #1; 
                data_out_q = data_out_q + 2;
            end
            default: begin
                wait(1'b0); 
            end
        endcase
    end
endmodule
