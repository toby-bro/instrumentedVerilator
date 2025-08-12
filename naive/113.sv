module SimpleLogic (
    input clk,
    input reset_n,
    input logic [7:0] data_in,
    input logic enable_reg,
    output logic [7:0] data_out_comb,
    output logic [7:0] data_out_seq
);
    parameter DATA_WIDTH = 8;
    localparam MAX_VALUE = 255;
    logic [DATA_WIDTH-1:0] internal_reg;
    assign data_out_comb = (data_in > (MAX_VALUE / 2)) ? data_in - (MAX_VALUE / 4) : data_in + (MAX_VALUE / 4);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            internal_reg <= '0;
            data_out_seq <= '0;
        end else if (enable_reg) begin
            internal_reg <= data_in;
            data_out_seq <= internal_reg + 1;
        end
    end
endmodule
module DataStructures (
    input logic [3:0] array_index_in,
    input logic [7:0] scalar_value_in,
    input logic [7:0] queue_push_val,
    input logic do_push,
    input logic do_pop,
    output logic [7:0] indexed_array_out,
    output logic [7:0] queue_front_out,
    output logic [7:0] array_sum_out
);
    typedef enum logic [1:0] {
        STATE_IDLE = 2'b00,
        STATE_PROCESSING = 2'b01,
        STATE_DONE = 2'b10
    } my_state_e;
    my_state_e current_state;
    typedef struct packed {
        logic [7:0] field_a;
        logic [3:0] field_b;
        bit         valid;
    } my_packed_struct_t;
    my_packed_struct_t unpacked_struct_var;
    logic [7:0] static_array [0:9];
    logic [7:0] dynamic_array [];
    logic [7:0] my_queue [$];
    always_comb begin
        unpacked_struct_var.field_a = scalar_value_in;
        unpacked_struct_var.field_b = array_index_in;
        unpacked_struct_var.valid = (scalar_value_in != '0);
        indexed_array_out = static_array[array_index_in % 10];
        array_sum_out = '0;
        for (int i = 0; i < 10; i++) begin
            static_array[i] = i * 2;
            array_sum_out += static_array[i];
        end
        if (dynamic_array.size() == 0) begin
            dynamic_array = new[5];
            foreach(dynamic_array[idx]) begin
                dynamic_array[idx] = idx + 100;
            end
        end
    end
    always_ff @(posedge unpacked_struct_var.valid) begin
        current_state <= (scalar_value_in == 8'hFF) ? STATE_DONE : STATE_PROCESSING;
    end
    always_ff @(posedge unpacked_struct_var.valid) begin
        if (do_push) begin
            my_queue.push_back(queue_push_val);
        end
        if (do_pop && my_queue.size() > 0) begin
            void'(my_queue.pop_front());
        end
        queue_front_out <= (my_queue.size() > 0) ? my_queue[0] : '0;
    end
endmodule
module ProceduralBlocks (
    input logic [7:0] input_a,
    input logic [7:0] input_b,
    input logic trigger_task,
    output logic [15:0] func_result_out,
    output logic [7:0] task_result_out
);
    typedef union packed {
        logic [15:0] word;
        struct packed {
            logic [7:0] lo_byte;
            logic [7:0] hi_byte;
        } bytes;
    } my_union_u;
    my_union_u union_var;
    function automatic logic [15:0] multiply_and_add(
        input logic [7:0] val1,
        input logic [7:0] val2
    );
        logic [15:0] temp_mul;
        temp_mul = val1 * val2;
        return temp_mul + 10;
    endfunction
    task automatic calculate_sum_task(
        input logic [7:0] val1,
        input logic [7:0] val2,
        output logic [7:0] sum_out
    );
        sum_out = val1 + val2;
    endtask
    always_comb begin
        func_result_out = multiply_and_add(input_a, input_b);
        union_var.word = func_result_out;
        if (trigger_task) begin
            calculate_sum_task(union_var.bytes.lo_byte, union_var.bytes.hi_byte, task_result_out);
        end else begin
            task_result_out = '0;
        end
    end
endmodule
module AdvancedFeatures #(
    parameter int SELECT_GEN_PARAM = 0
) (
    input clk,
    input logic reset,
    input logic [7:0] config_value,
    input logic run_class_op,
    output logic [7:0] class_output_val,
    output logic [7:0] generated_output_val
);
    class MyDataProcessor;
        rand int m_data;
        int m_offset;
        constraint c_data { m_data inside {[0:100]}; }
        function new(int offset);
            this.m_offset = offset;
        endfunction
        function int process_data(int input_val);
            int temp;
            if (!this.randomize()) begin
                temp = input_val + m_offset;
            end else begin
                temp = input_val + m_offset + m_data;
            end
            return temp;
        endfunction
    endclass
    MyDataProcessor my_processor_handle;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            my_processor_handle = null;
            class_output_val <= '0;
        end else if (run_class_op) begin
            if (my_processor_handle == null) begin
                my_processor_handle = new(config_value);
            end
            class_output_val <= my_processor_handle.process_data(config_value);
        end else begin
            class_output_val <= '0;
        end
    end
    generate
        if (SELECT_GEN_PARAM == 0) begin : gen_block_zero
            assign generated_output_val = config_value + 5;
        end else if (SELECT_GEN_PARAM == 1) begin : gen_block_one
            assign generated_output_val = config_value * 2;
        end else begin : gen_block_else
            assign generated_output_val = config_value - 1;
        end
    endgenerate
endmodule
module ComplexGenerate (
    input logic [3:0] gen_index_in,
    input logic [7:0] data_value_in,
    output logic [7:0] processed_data_out,
    output logic [7:0] indexed_param_out
);
    parameter NUM_INSTANCES = 4;
    parameter logic [7:0] PARAM_ARRAY [NUM_INSTANCES-1:0] = {8'h10, 8'h20, 8'h30, 8'h40};
    logic [7:0] internal_calc_result [NUM_INSTANCES-1:0];
    generate
        genvar i;
        for (i = 0; i < NUM_INSTANCES; i = i + 1) begin : gen_calc
            if (i % 2 == 0) begin
                assign internal_calc_result[i] = data_value_in + i;
            end else begin
                assign internal_calc_result[i] = data_value_in - i;
            end
        end
    endgenerate
    assign processed_data_out = internal_calc_result[gen_index_in % NUM_INSTANCES];
    assign indexed_param_out = PARAM_ARRAY[gen_index_in % NUM_INSTANCES];
endmodule
module AssertionModule (
    input clk,
    input logic a_in,
    input logic b_in,
    output logic c_out,
    output logic some_internal_flag
);
    logic internal_state;
    logic prev_a_in;
    always_ff @(posedge clk) begin
        internal_state <= a_in && b_in;
        c_out <= internal_state;
        prev_a_in <= a_in;
    end
    always_comb begin
        assert (a_in || b_in);
    end
    property p_a_prev_implies_b_curr;
        @(posedge clk) prev_a_in |-> b_in;
    endproperty
    assert property (p_a_prev_implies_b_curr);
    property p_c_out_valid;
        @(posedge clk) $isunknown(c_out) == 1'b0;
    endproperty
    assert property (p_c_out_valid);
    assign some_internal_flag = a_in ^ b_in;
endmodule
