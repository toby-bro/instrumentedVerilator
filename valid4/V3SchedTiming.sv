package my_timing_pkg;
  class MyClass_Timing;
      int class_member_q;
      int internal_state_q;
      function new();
          class_member_q = 0;
          internal_state_q = 0;
      endfunction
      task complex_operation(input int val);
          fork : class_inner_fork
              begin : class_sub_op_a
                  int temp_val;
                  temp_val = val + 10;
                  class_member_q = temp_val;
                  internal_state_q = 1;
              end
              begin : class_sub_op_b
                  int another_val;
                  another_val = val * 2;
                  internal_state_q = internal_state_q + another_val;
              end
          join_none
      endtask
  endclass
endpackage
module ForkAwaitVarModule (
    input logic clk,
    input int in_data,
    output int out_result
);
    logic [7:0] local_a, local_b;
    logic       flag_async;
    always_ff @(posedge clk) begin
        local_a <= in_data + 1;
        flag_async <= 1'b0;
    end
    always_comb begin
        out_result = 0;
        fork : my_main_fork
            begin : block_one
                int temp_fork_var;
                temp_fork_var = in_data * 2;
                local_b = temp_fork_var + 3;
                flag_async = 1'b1;
            end
            begin : block_two
                int another_var;
                another_var = in_data - 1;
                out_result = another_var + local_a;
            end
        join_none
        wait fork;
    end
endmodule
module NamedBeginForkModule (
    input logic rst_n,
    input int input_val,
    output int output_sum
);
    int sum_local;
    int loop_count;
    always_comb begin
        sum_local = 0;
        loop_count = input_val % 5;
        if (rst_n) begin
            fork
                begin : calculate_block_a
                    int temp_a;
                    temp_a = input_val + loop_count;
                    sum_local = sum_local + temp_a;
                end
                begin : calculate_block_b
                    int temp_b;
                    temp_b = input_val * 2 - loop_count;
                    sum_local = sum_local + temp_b;
                end
                begin : calculate_block_c
                    int temp_c = input_val / 2;
                    sum_local = sum_local + temp_c;
                end
            join_any
            wait fork;
            output_sum = sum_local;
        end else begin
            output_sum = 0;
        end
    end
endmodule
module TimingSchedulerModule (
    input logic clk,
    input logic rst_n,
    input int data_in,
    output int data_out_ff,
    output int data_out_comb,
    output int data_out_proc_result
);
    logic [15:0] reg_a;
    logic [15:0] combo_val;
    logic [15:0] proc_delay_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            reg_a <= 16'h0000;
            data_out_ff <= 0;
            proc_delay_reg <= 0;
        end else begin
            reg_a <= data_in;
            data_out_ff <= reg_a + 1;
            fork : timing_process
                begin
                    proc_delay_reg <= data_in + 5;
                end
                begin
                    proc_delay_reg <= proc_delay_reg + 1;
                end
            join_none
        end
    end
    always_comb begin
        combo_val = data_in * 3;
        data_out_comb = combo_val;
        data_out_proc_result = proc_delay_reg;
    end
endmodule
module ClassForkModule (
    input logic clk,
    input logic rst_n,
    input logic enable_cls,
    input int cls_data_in,
    output int cls_data_out
);
    import my_timing_pkg::*;
    my_timing_pkg::MyClass_Timing my_instance_r;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            my_instance_r = null;
        end else if (enable_cls) begin
            if (my_instance_r == null) begin
                my_instance_r = new my_timing_pkg::MyClass_Timing();
            end
            if (my_instance_r != null) begin
                my_instance_r.complex_operation(cls_data_in);
            end
        end
    end
    always_comb begin
        if (my_instance_r != null) begin
            cls_data_out = my_instance_r.class_member_q + my_instance_r.internal_state_q;
        end else begin
            cls_data_out = 0;
        end
    end
endmodule
