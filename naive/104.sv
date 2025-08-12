module LogicAndDatatypes (
    input logic [7:0] in_data,
    input bit         in_clk_en,
    output logic [15:0] out_sum,
    output logic [3:0] out_enum_val
);
    typedef enum logic [3:0] {
        STATE_IDLE   = 4'h0,
        STATE_ACTIVE = 4'h1,
        STATE_DONE   = 4'h2,
        STATE_ERROR  = 4'hF
    } my_state_e;
    my_state_e current_state;
    logic [7:0] internal_reg_val;
    int         loop_counter;
    always_ff @(posedge in_clk_en) begin
        case (current_state)
            STATE_IDLE: begin
                internal_reg_val <= in_data;
                current_state    <= STATE_ACTIVE;
                loop_counter     <= 0;
            end
            STATE_ACTIVE: begin
                internal_reg_val <= internal_reg_val + 1;
                loop_counter     <= loop_counter + 1;
                if (loop_counter >= 15) begin
                    current_state <= STATE_DONE;
                end
            end
            STATE_DONE: begin
                current_state <= STATE_IDLE;
                internal_reg_val <= 0;
                loop_counter <= 0;
            end
            default: begin
                current_state <= STATE_ERROR;
                internal_reg_val <= 8'hFF;
                loop_counter <= -1;
            end
        endcase
    end
    assign out_sum = ({1'b0, in_data} <<< 8) + {8'b0, internal_reg_val};
    assign out_enum_val = current_state;
endmodule
module ComplexArithmetic (
    input real in_real_input,
    input int  in_iterations,
    output real out_real_scaled,
    output int  out_accumulated_sum
);
    localparam real PI_VAL = 3.1415926535;
    real temp_real_calc;
    int  accum_sum;
    always_comb begin
        temp_real_calc = in_real_input * PI_VAL;
        out_real_scaled = (in_real_input != 0.0) ? (temp_real_calc / in_real_input) : PI_VAL;
        accum_sum = 0;
        for (int i = 0; i < in_iterations; i++) begin
            accum_sum = accum_sum + i;
        end
        out_accumulated_sum = accum_sum;
    end
endmodule
package MyClassesPkg;
    class MyBaseProcessor;
        protected int m_base_value;
        function new();
            m_base_value = 10;
        endfunction
        virtual function automatic int process_value(int input_val);
            return input_val + m_base_value;
        endfunction
        function automatic void set_base_value(int new_val);
            m_base_value = new_val;
        endfunction
    endclass
    class MyDerivedProcessor extends MyBaseProcessor;
        int m_factor;
        function new();
            super.new();
            m_factor = 2;
        endfunction
        function automatic int process_value(int input_val);
            return super.process_value(input_val) * m_factor;
        endfunction
    endclass
endpackage
import MyClassesPkg::*;
module ClassProcessor (
    input int in_data_val,
    input bit in_init_trigger,
    output int out_result_val
);
    MyBaseProcessor base_proc_handle;
    MyDerivedProcessor derived_proc_handle;
    int temp_result;
    always_comb begin
        if (in_init_trigger) begin
            base_proc_handle = new();
            base_proc_handle.set_base_value(in_data_val % 50 + 1);
            derived_proc_handle = new();
            derived_proc_handle.set_base_value(in_data_val % 100 + 1);
        end else begin
            if (base_proc_handle == null) begin
                base_proc_handle = new();
            end
            if (derived_proc_handle == null) begin
                derived_proc_handle = new();
            end
        end
        if (base_proc_handle != null) begin
            temp_result = base_proc_handle.process_value(in_data_val);
        end else begin
            temp_result = 0;
        end
        if (derived_proc_handle != null) begin
            temp_result += derived_proc_handle.process_value(in_data_val / 2);
        end
        out_result_val = temp_result;
    end
endmodule
module AdvancedArrays (
    input logic [15:0] in_packed_val,
    input int          in_unpacked_idx,
    output logic [7:0] out_unpacked_elem,
    output int         out_queue_sum
);
    typedef logic [3:0] nibble_t;
    nibble_t packed_data [4];
    logic [7:0] unpacked_memory [0:7];
    string string_map [int];
    byte dynamic_bytes[];
    int value_queue [$];
    always_comb begin
        int sum_queue;
        sum_queue = 0;
        packed_data[0] = in_packed_val[3:0];
        packed_data[1] = in_packed_val[7:4];
        packed_data[2] = in_packed_val[11:8];
        packed_data[3] = in_packed_val[15:12];
        for (int i = 0; i < 8; i++) begin
            unpacked_memory[i] = i * 2 + 1;
        end
        if (in_unpacked_idx >= 0 && in_unpacked_idx < 8) begin
            out_unpacked_elem = unpacked_memory[in_unpacked_idx];
        end else begin
            out_unpacked_elem = 8'hXX;
        end
        string_map[10] = "First";
        string_map[20] = "Second";
        string_map[30] = "Third";
        string_map.delete(20);
        value_queue.push_back(5);
        value_queue.push_front(1);
        value_queue.push_back(10);
        value_queue.insert(1, 2);
        value_queue.delete(3);
        if (value_queue.size() > 0) begin
            foreach (value_queue[idx]) begin
                sum_queue += value_queue[idx];
            end
            void'(value_queue.pop_front());
        end
        out_queue_sum = sum_queue;
        dynamic_bytes = new[4];
        for (int i = 0; i < dynamic_bytes.size(); i++) begin
            dynamic_bytes[i] = i * 3;
        end
        dynamic_bytes.delete();
        if (string_map.exists(10)) begin
        end
    end
endmodule
module ParameterizedLogic #(
    parameter ADDR_WIDTH = 4,
    parameter ENABLE_REG = 1
) (
    input logic [ADDR_WIDTH-1:0] in_addr,
    input logic                  in_read_en,
    output logic [7:0]           out_data
);
    logic [7:0] registered_data;
    logic [7:0] my_mem [1<<ADDR_WIDTH];
    logic [ADDR_WIDTH-1:0] generated_bits;
    always_comb begin
        for (int i = 0; i < (1<<ADDR_WIDTH); i++) begin
            automatic logic [7:0] current_val = i * 5 + (in_addr[0] ? 1 : 0);
            if (i < ADDR_WIDTH / 2) begin
                current_val[0] = ~in_addr[i];
            end
            my_mem[i] = current_val;
        end
    end
    genvar gv_idx;
    generate
        for (gv_idx = 0; gv_idx < ADDR_WIDTH; gv_idx++) begin : bit_copy_block
            assign generated_bits[gv_idx] = in_addr[gv_idx];
        end
    endgenerate
    generate
        if (ENABLE_REG) begin : data_register_block
            always_ff @(posedge in_read_en) begin
                registered_data <= my_mem[in_addr] ^ {7'b0, generated_bits[0]};
            end
            assign out_data = registered_data;
        end else begin : direct_access_block
            assign out_data = my_mem[in_addr] ^ {7'b0, generated_bits[0]};
        end
    endgenerate
endmodule
interface MySimpleInterface (input bit clk);
    logic [7:0] data;
    logic       valid;
    logic       ready;
    modport Producer (output data, output valid, input ready, input clk);
    modport Consumer (input data, input valid, output ready, input clk);
endinterface
module InterfaceUser (
    input bit                   sys_clock,
    input logic [7:0]           in_data_to_producer,
    output logic [7:0]          out_data_from_consumer,
    output logic                out_consumer_ready_flag
);
    MySimpleInterface my_if (.clk(sys_clock));
    always_comb begin
        my_if.data  = in_data_to_producer;
        my_if.valid = 1'b1;
    end
    always_comb begin
        out_data_from_consumer  = my_if.data;
        out_consumer_ready_flag = my_if.valid;
    end
endmodule
module FuncTaskModule (
    input logic [15:0] in_operand_a,
    input logic [15:0] in_operand_b,
    input bit          in_operation_sel,
    output logic [31:0] out_calculated_result
);
    function automatic logic [15:0] perform_addition (
        logic [15:0] op1,
        logic [15:0] op2
    );
        logic [15:0] sum_temp;
        sum_temp = op1 + op2;
        return sum_temp;
    endfunction
    function static logic [31:0] perform_multiplication (
        logic [15:0] op1,
        logic [15:0] op2
    );
        logic [31:0] prod_temp;
        prod_temp = op1 * op2;
        return prod_temp;
    endfunction
    task automatic calculate_final_result (
        input logic [15:0] val1,
        input logic [15:0] val2,
        input bit          selector,
        output logic [31:0] final_res
    );
        if (selector == 1'b0) begin
            final_res = perform_addition(val1, val2);
        end else begin
            final_res = perform_multiplication(val1, val2);
        end
    endtask
    always_comb begin
        calculate_final_result(in_operand_a, in_operand_b, in_operation_sel, out_calculated_result);
    end
endmodule
module ImmediateAssertionModule (
    input logic [7:0] in_data_a,
    input logic [7:0] in_data_b,
    output logic      out_a_eq_b,
    output logic      out_sum_gt_100
);
    logic [8:0] sum_val;
    always_comb begin
        sum_val = in_data_a + in_data_b;
        assert (in_data_a == in_data_b) else begin end;
        out_a_eq_b = (in_data_a == in_data_b);
        assert (sum_val > 8'd100) else begin end;
        out_sum_gt_100 = (sum_val > 8'd100);
        assert (in_data_a < 256);
    end
endmodule
