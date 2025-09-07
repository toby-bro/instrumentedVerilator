interface SimpleBus(input logic clk);
    logic [7:0] addr;
    logic [7:0] data;
    logic       read_en;
    logic       write_en;
    modport Master (output addr, output data, output read_en, output write_en);
    modport Slave  (input addr, input data, input read_en, input write_en);
endinterface
module SubModule (
    SimpleBus.Slave bus_if,
    input logic enable_sub,
    output logic [7:0] sub_output
);
    logic [7:0] internal_data;
    always_comb begin : sub_logic_named_block
        if (enable_sub) begin
            internal_data = bus_if.data + bus_if.addr;
        end
        else begin
            internal_data = 8'h00;
        end
    end
    assign sub_output = internal_data;
endmodule
module NamedBlocksAndFork (
    input logic clk,
    input logic rst_n,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    typedef enum { IDLE, RUN } State_t;
    always_ff @(posedge clk or negedge rst_n) begin : ff_process_block
        if (!rst_n) begin : reset_handling
            data_out <= 8'h00;
        end
        else begin : data_path_logic
            data_out <= data_in;
        end
    end
    always_comb begin : combinational_fork_block
        fork : my_concurrent_group
            begin : task_like_block_1
                typedef struct packed {
                    logic [3:0] field1;
                    logic [3:0] field2;
                } my_struct_type;
                my_struct_type local_struct_var;
                local_struct_var.field1 = data_in[3:0];
                local_struct_var.field2 = data_in[7:4];
            end
            begin : task_like_block_2
                logic [7:0] temporary_data_var;
                temporary_data_var = data_in;
            end
        join_none
    end
endmodule
module ForeachExamples (
    input logic [7:0] data_arr_in [0:3],
    input logic [7:0] dynamic_data_in,
    input logic [7:0] queue_data_in,
    input logic [7:0] assoc_key_in,
    input logic [7:0] assoc_val_in,
    input string string_in,
    output logic [7:0] sum_fixed,
    output logic [7:0] sum_dynamic,
    output logic [7:0] sum_queue,
    output logic [7:0] sum_assoc,
    output logic [7:0] sum_string
);
    logic [7:0] local_sum_fixed = 0;
    logic [7:0] local_sum_dynamic = 0;
    logic [7:0] local_sum_queue = 0;
    logic [7:0] local_sum_assoc = 0;
    logic [7:0] local_sum_string = 0;
    always_comb begin : fixed_array_summation
        local_sum_fixed = 0;
        foreach (data_arr_in[i]) begin : foreach_fixed_item
            local_sum_fixed += data_arr_in[i];
        end
        sum_fixed = local_sum_fixed;
    end
    logic [7:0] dyn_arr[];
    initial begin : dynamic_array_setup
        dyn_arr = new [4];
        dyn_arr[0] = dynamic_data_in;
        dyn_arr[1] = dynamic_data_in + 1;
        dyn_arr[2] = dynamic_data_in + 2;
        dyn_arr[3] = dynamic_data_in + 3;
    end
    always_comb begin : dynamic_array_summation
        local_sum_dynamic = 0;
        foreach (dyn_arr[idx]) begin : foreach_dyn_item
            local_sum_dynamic += dyn_arr[idx];
        end
        sum_dynamic = local_sum_dynamic;
    end
    logic [7:0] q_arr[$];
    initial begin : queue_setup
        q_arr.push_back(queue_data_in);
        q_arr.push_back(queue_data_in + 1);
        q_arr.push_back(queue_data_in + 2);
    end
    always_comb begin : queue_summation
        local_sum_queue = 0;
        foreach (q_arr[jdx]) begin : foreach_q_item
            local_sum_queue += q_arr[jdx];
        end
        sum_queue = local_sum_queue;
    end
    logic [7:0] assoc_arr[logic [7:0]];
    initial begin : associative_array_setup
        assoc_arr[assoc_key_in] = assoc_val_in;
        assoc_arr[assoc_key_in + 1] = assoc_val_in + 1;
    end
    always_comb begin : associative_array_summation
        local_sum_assoc = 0;
        foreach (assoc_arr[key]) begin : foreach_assoc_item
            local_sum_assoc += assoc_arr[key];
        end
        sum_assoc = local_sum_assoc;
    end
    always_comb begin : string_character_sum
        local_sum_string = 0;
        foreach (string_in[k]) begin : foreach_string_char
            local_sum_string += string_in[k];
        end
        sum_string = local_sum_string;
    end
endmodule
module FuncTaskIfCover (
    input logic [3:0] control_in,
    input logic enable_func,
    input logic enable_task,
    output logic [7:0] func_out,
    output logic task_done
);
    function automatic logic [7:0] my_func (input logic [3:0] val);
        static int static_call_count = 0;
        static_call_count++;
        if (enable_func) begin : func_execution_block_1
            if (val == 4'h1) begin : func_execution_block_2
                if (val[0]) begin : func_execution_block_3
                    my_func = val + static_call_count;
                end
                else begin : func_execution_block_4
                    my_func = val + static_call_count + 1;
                end
            end
            else begin : func_execution_block_5
                my_func = 8'hFF;
            end
        end
        else begin : func_execution_block_6
            my_func = 8'h00;
        end
    endfunction
    task automatic my_task (input logic [3:0] value_in);
        logic [7:0] temp_accum;
        temp_accum = 0;
        begin : task_internal_logic
            temp_accum = value_in + 10;
        end
        task_done = (temp_accum > 15);
        if (value_in == 4'hA) unique begin : unique_branch
            task_done = 1'b1;
        end else if (value_in == 4'hB) priority begin : priority_branch
            task_done = 1'b0;
        end else begin : default_branch
            task_done = 1'b1;
        end
    endtask
    assign func_out = my_func(control_in);
    always_comb begin : task_call_block
        task_done = 1'b0;
        if (enable_task) begin
            my_task(control_in);
        end
    end
    covergroup my_covergroup @(control_in);
        cp_control : coverpoint control_in {
            bins low_range = {0, 1};
            bins high_range = {14, 15};
        }
        cp_func_output : coverpoint func_out;
    endgroup
    my_covergroup cg_inst = new();
endmodule
module TopModuleInst (
    input logic main_clk,
    input logic main_enable,
    input logic [7:0] main_addr,
    input logic [7:0] main_data,
    output logic [7:0] final_output,
    output logic [7:0] hier_output
);
    SimpleBus bus_inst (main_clk);
    SubModule sub_inst (
        .bus_if(bus_inst),
        .enable_sub(main_enable),
        .sub_output(final_output)
    );
    always_comb begin : bus_interface_driver
        bus_inst.addr = main_addr;
        bus_inst.data = main_data;
        bus_inst.read_en = 1'b1;
        bus_inst.write_en = 1'b0;
    end
    assign hier_output = sub_inst.sub_output + bus_inst.addr;
    always_comb begin : module_local_logic
        logic [7:0] temporary_calc_val;
        temporary_calc_val = final_output + 1;
    end
endmodule
