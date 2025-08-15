module shadow_var_simple (
    input clk,
    input rst,
    input [7:0] in_data,
    output logic [7:0] out_data
);
    logic [7:0] s_var_reg;
    always_ff @(posedge clk) begin
        if (rst) begin
            s_var_reg <= 8'h00;
        end else begin
            s_var_reg <= in_data;
        end
    end
    assign out_data = s_var_reg;
endmodule
module shadow_var_masked_mixed_updates (
    input clk,
    input rst,
    input [7:0] in_packed_val_nba,
    input [2:0] in_packed_idx_nba,
    input [7:0] in_packed_val_blk,
    input [2:0] in_packed_idx_blk,
    input comb_enable,
    output logic [7:0] out_packed_vec
);
    logic [7:0] packed_reg;
    always_ff @(posedge clk) begin
        if (rst) begin
            packed_reg <= 8'h00;
        end else begin
            packed_reg[in_packed_idx_nba +: 4] <= in_packed_val_nba[3:0];
        end
    end
    always_comb begin
        if (comb_enable)
            packed_reg[in_packed_idx_blk +: 4] = in_packed_val_blk[3:0];
    end
    assign out_packed_vec = packed_reg;
endmodule
module flag_shared_unpacked_array (
    input clk,
    input rst,
    input [1:0] arr_idx1,
    input [7:0] arr_val1,
    input [1:0] arr_idx2,
    input [7:0] arr_val2,
    output logic [7:0] out_unpacked_arr_sum
);
    logic [7:0] unpacked_arr [0:3];
    always_ff @(posedge clk) begin
        if (rst) begin
            for (int i=0; i<4; i++) unpacked_arr[i] <= 8'h00;
        end else begin
            unpacked_arr[arr_idx1] <= arr_val1;
            unpacked_arr[arr_idx2] <= arr_val2;
        end
    end
    assign out_unpacked_arr_sum = unpacked_arr[0] + unpacked_arr[1] + unpacked_arr[2] + unpacked_arr[3];
endmodule
module flag_unique_suspendable_non_packed_mixed (
    input clk,
    input rst,
    input [7:0] data_in_a,
    input bit data_in_b,
    output logic [7:0] data_out_a,
    output bit data_out_b
);
    logic [7:0] my_data_reg_a;
    bit my_data_reg_b;
    always_ff @(posedge clk) begin
        if (rst) begin
            my_data_reg_a <= 8'h00;
            my_data_reg_b <= 1'b0;
        end else begin
            fork
                my_data_reg_a <= data_in_a;
                my_data_reg_b <= data_in_b;
            join_none
        end
    end
    assign data_out_a = my_data_reg_a;
    assign data_out_b = my_data_reg_b;
endmodule
module value_queue_whole_loop_test (
    input clk,
    input rst,
    input [7:0] loop_val,
    input [1:0] loop_idx_base,
    output logic [7:0] out_arr_val
);
    logic [7:0] my_unpacked_q_arr [0:7];
    always_ff @(posedge clk) begin
        if (rst) begin
            for (int i=0; i<8; i++) my_unpacked_q_arr[i] <= 8'h00;
        end else begin
            for (int i=0; i<4; i++) begin
                my_unpacked_q_arr[loop_idx_base + i] <= loop_val + i;
            end
        end
    end
    assign out_arr_val = my_unpacked_q_arr[0];
endmodule
module value_queue_partial_loop_test (
    input clk,
    input rst,
    input [7:0] loop_val,
    input [1:0] loop_idx_base,
    input [3:0] bit_sel_start,
    output logic [15:0] out_arr_val_partial
);
    logic [15:0] my_unpacked_q_arr_p [0:7];
    always_ff @(posedge clk) begin
        if (rst) begin
            for (int i=0; i<8; i++) my_unpacked_q_arr_p[i] <= 16'h0000;
        end else begin
            for (int i=0; i<4; i++) begin
                my_unpacked_q_arr_p[loop_idx_base + i][bit_sel_start +: 4] <= (loop_val + i)[3:0];
            end
        end
    end
    assign out_arr_val_partial = my_unpacked_q_arr_p[0];
endmodule
module unsupported_compound_array_in_loop_warn (
    input clk,
    input rst,
    input [1:0] idx_in,
    input [7:0] val_a_in,
    output logic [7:0] out_val_a
);
    typedef struct packed {
        logic [7:0] fA;
        logic [7:0] fB;
    } my_struct_t;
    my_struct_t unpacked_struct_arr [0:3];
    always_ff @(posedge clk) begin
        if (rst) begin
            for (int i=0; i<4; i++) begin
                unpacked_struct_arr[i].fA <= 8'h00;
                unpacked_struct_arr[i].fB <= 8'h00;
            end
        end else begin
            for (int i=0; i<4; i++) begin
                unpacked_struct_arr[idx_in + i].fA <= val_a_in;
            end
        end
    end
    assign out_val_a = unpacked_struct_arr[0].fA;
endmodule
module func_task_delayed_warning_and_events (
    input clk,
    input rst,
    input [7:0] task_data_in,
    input trigger_event,
    output logic [7:0] task_data_out,
    output logic [7:0] fork_data_out,
    output bit event_triggered_out
);
    logic [7:0] task_internal_reg;
    logic [7:0] fork_internal_reg;
    event my_simple_event;
    logic my_event_triggered_ff;
    task automatic my_nba_task(input [7:0] t_in);
        task_internal_reg <= t_in;
    endtask
    always_ff @(posedge clk) begin
        if (rst) begin
            task_internal_reg <= 8'h00;
            fork_internal_reg <= 8'h00;
            my_event_triggered_ff <= 1'b0;
        end else begin
            my_nba_task(task_data_in);
            fork
                fork_internal_reg <= fork_internal_reg + 1;
                if (trigger_event) begin
                    -> my_simple_event;
                end
            join_none
            if (my_simple_event.triggered) begin
                my_event_triggered_ff <= 1'b1;
            end
        end
    end
    assign task_data_out = task_internal_reg;
    assign fork_data_out = fork_internal_reg;
    assign event_triggered_out = my_event_triggered_ff;
endmodule
