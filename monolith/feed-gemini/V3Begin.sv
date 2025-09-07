interface my_simple_if (input bit clk);
    logic [7:0] data;
    logic valid;
    modport master (output data, output valid);
    modport slave (input data, input valid);
endinterface
module block_inliner (
    input logic i_clk,
    input logic i_reset,
    input logic i_data,
    output logic o_result
);
    logic internal_var_a;
    typedef enum {STATE_IDLE, STATE_RUN} FSM_STATE_T;
    FSM_STATE_T current_state;
    always_ff @(posedge i_clk or posedge i_reset) begin : main_block
        if (i_reset) begin : reset_block
            internal_var_a = 1'b0;
            o_result = 1'b0;
            current_state = STATE_IDLE;
        end else begin : active_block
            begin
                logic temp_b;
                temp_b = i_data;
                internal_var_a = temp_b;
            end
            begin : computation_block
                logic [3:0] loop_idx;
                typedef struct { logic [7:0] data; bit valid; } PACKET_T;
                PACKET_T my_packet;
                my_packet.valid = 1'b1;
                my_packet.data = {4'b0, i_data, internal_var_a, 1'b0};
                for (loop_idx = 0; loop_idx < 4; loop_idx++) begin : loop_body
                    if (loop_idx == 2) begin
                        o_result = my_packet.valid;
                    end
                end
                current_state = (current_state == STATE_IDLE) ? STATE_RUN : STATE_IDLE;
            end
        end
    end
endmodule
module task_func_static (
    input logic i_enable,
    input logic [7:0] i_value,
    output logic [7:0] o_output
);
    function automatic [7:0] increment_and_accumulate(input [7:0] val);
        static int accumulator_static = 0;
        accumulator_static += val;
        return accumulator_static;
    endfunction
    task my_task(input [7:0] in_val, output [7:0] out_val);
        static int task_counter_static = 0;
        task_counter_static++;
        out_val = in_val + task_counter_static;
    endtask
    always_comb begin : logic_block
        begin : call_block
            logic [7:0] task_res;
            if (i_enable) begin
                o_output = increment_and_accumulate(i_value);
                my_task(i_value, task_res);
                o_output = o_output + task_res;
            end else begin
                o_output = 8'h00;
            end
        end
    end
endmodule
module foreach_converter (
    input logic i_clk,
    input logic i_reset,
    input logic i_trigger,
    output logic o_done
);
    logic [7:0] fixed_array [0:3];
    logic [7:0] dynamic_array [];
    logic [7:0] queue_array [$];
    logic [7:0] assoc_array [int];
    string my_string;
    logic [3:0] sum_val;
    always_ff @(posedge i_clk or posedge i_reset) begin : main_process
        if (i_reset) begin
            fixed_array = '{0,1,2,3};
            dynamic_array = new[2] ('{4,5});
            queue_array = {6,7,8};
            my_string = "Hello";
            assoc_array[10] = 9;
            assoc_array[11] = 8;
            o_done = 1'b0;
            sum_val = 0;
        end else if (i_trigger) begin : trigger_block
            sum_val = 0;
            foreach (fixed_array[idx]) begin : fixed_loop
                sum_val += fixed_array[idx];
            end
            foreach (dynamic_array[jdx]) begin : dynamic_loop
                sum_val += dynamic_array[jdx];
            end
            foreach (queue_array[kdx]) begin : queue_loop
                sum_val += queue_array[kdx];
            end
            foreach (assoc_array[key]) begin : assoc_loop
                sum_val += assoc_array[key];
            end
            foreach (my_string[s_idx]) begin : string_loop
                sum_val += my_string[s_idx];
            end
            o_done = 1'b1;
        end
    end
endmodule
module fork_if_coverage (
    input logic i_clk,
    input logic i_reset,
    input logic [1:0] i_mode,
    output logic o_status
);
    logic fork_result_a;
    logic fork_result_b;
    logic [3:0] if_depth_val;
    covergroup cg_mode @(posedge i_clk);
        mode_cp : coverpoint i_mode;
    endgroup
    cg_mode cg_inst;
    initial begin
        cg_inst = new();
    end
    always_ff @(posedge i_clk or posedge i_reset) begin : main_fsm
        if (i_reset) begin
            fork_result_a = 1'b0;
            fork_result_b = 1'b0;
            o_status = 1'b0;
            if_depth_val = 4'b0;
        end else begin
            fork
                begin : fork_task_a
                    fork_result_a = i_mode[0];
                end
                begin : fork_task_b
                    fork_result_b = i_mode[1];
                end
            join_none
            if (i_mode == 2'b00) begin : mode0_block
                if_depth_val = 4'd0;
            end else if (i_mode == 2'b01) begin : mode1_block
                if (i_mode[0] == 1'b1) begin : sub_mode1_block
                    unique if (i_mode[1] == 1'b0) begin
                        if_depth_val = 4'd1;
                    end else begin
                        if_depth_val = 4'd2;
                    end
                end
            end else if (i_mode == 2'b10) begin : mode2_block
                if (i_mode[1] == 1'b1) begin : sub_mode2_block
                    priority if (i_mode[0] == 1'b0) begin
                        if_depth_val = 4'd3;
                    end else begin
                        if_depth_val = 4'd4;
                    end
                end
            end else begin : mode3_block
                if (i_mode == 2'b11) begin : sub_mode3_block
                    if_depth_val = 4'd5;
                    if (fork_result_a) begin
                        if (fork_result_b) begin
                            if (o_status) begin
                                if_depth_val = 4'd6;
                            end
                        end
                    end
                end
            end
            o_status = fork_result_a ^ fork_result_b;
        end
    end
endmodule
module hierarchical_scopes (
    input logic i_clk,
    input logic i_reset,
    input logic [7:0] i_main_data,
    output logic [7:0] o_final_data,
    output logic o_if_valid
);
    my_simple_if if_inst (i_clk);
    logic [7:0] data_from_sub;
    generate
        if (1) begin : gen_sub_instance_block
            sub_module_if_type sub_inst (
                .i_clk(i_clk),
                .i_reset(i_reset),
                .i_data(i_main_data),
                .o_data(data_from_sub),
                .io_if(if_inst)
            );
        end
    endgenerate
    always_comb begin : output_logic
        o_final_data = i_main_data + data_from_sub + if_inst.data;
        o_if_valid = if_inst.valid;
    end
endmodule
module sub_module_if_type (
    input logic i_clk,
    input logic i_reset,
    input logic [7:0] i_data,
    output logic [7:0] o_data,
    my_simple_if.master io_if
);
    logic [7:0] internal_sub_var;
    always_ff @(posedge i_clk or posedge i_reset) begin : sub_main_block
        if (i_reset) begin
            internal_sub_var = 8'h0;
            o_data = 8'h0;
            io_if.data = 8'h0;
            io_if.valid = 1'b0;
        end else begin
            internal_sub_var = i_data + 8'h1;
            o_data = internal_sub_var;
            io_if.data = internal_sub_var + 8'h2;
            io_if.valid = 1'b1;
        end
    end
endmodule
