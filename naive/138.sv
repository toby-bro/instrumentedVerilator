module BasicCombinationalLogic (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic sel_op,
    output logic [8:0] out_sum,
    output logic out_and_or,
    output logic [7:0] out_mux
);
    logic [7:0] intermediate_val;
    assign out_sum = in_a + in_b;
    assign out_and_or = (in_a[0] & in_b[0]) | sel_op;
    assign intermediate_val = (in_a > in_b) ? in_a : in_b;
    assign out_mux = sel_op ? in_a : intermediate_val;
endmodule
module SimpleFSM (
    input logic clk,
    input logic reset_n,
    input logic start_task,
    output logic [3:0] current_state_out,
    output logic task_done
);
    typedef enum logic [1:0] {
        IDLE,
        INIT,
        PROCESS,
        DONE
    } fsm_state_e;
    fsm_state_e current_state, next_state;
    parameter IDLE_VAL = 4'h0;
    parameter INIT_VAL = 4'h1;
    parameter PROCESS_VAL = 4'h2;
    parameter DONE_VAL = 4'h3;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            current_state <= IDLE;
        end else begin
            current_state <= next_state;
        end
    end
    always_comb begin
        next_state = current_state;
        task_done = 1'b0;
        current_state_out = IDLE_VAL;
        case (current_state)
            IDLE: begin
                current_state_out = IDLE_VAL;
                if (start_task) begin
                    next_state = INIT;
                end
            end
            INIT: begin
                current_state_out = INIT_VAL;
                next_state = PROCESS;
            end
            PROCESS: begin
                current_state_out = PROCESS_VAL;
                next_state = DONE;
            end
            DONE: begin
                current_state_out = DONE_VAL;
                task_done = 1'b1;
                if (!start_task) begin
                    next_state = IDLE;
                end
            end
            default: begin
                next_state = IDLE;
                current_state_out = 4'hF;
            end
        endcase
    end
endmodule
module DataStructureProcessor (
    input logic in_data_ready,
    input logic [15:0] in_value,
    output logic out_processed_valid,
    output logic [31:0] out_total_sum
);
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
    } my_packed_struct_t;
    typedef struct {
        int         count;
        logic [15:0] data;
        my_packed_struct_t packed_item;
    } my_unpacked_struct_t;
    my_unpacked_struct_t data_storage[4];
    logic [7:0] byte_array[2][2];
    logic [15:0] processed_value;
    logic [31:0] internal_sum;
    function automatic logic [15:0] process_value(logic [15:0] val);
        logic [15:0] processed_val_local = val;
        for (int i = 0; i < 4; i++) begin
            processed_val_local = processed_val_local + 1;
        end
        return processed_val_local;
    endfunction
    assign processed_value = process_value(in_value);
    always_comb begin
        out_processed_valid = 1'b0;
        out_total_sum = 32'h0;
        internal_sum = 32'h0;
        if (in_data_ready) begin
            for (int i = 0; i < 4; i++) begin
                data_storage[i].count = i;
                data_storage[i].data = processed_value + i;
                data_storage[i].packed_item.field_a = i + 10;
                data_storage[i].packed_item.field_b = i + 20;
                internal_sum = internal_sum + data_storage[i].data;
            end
            byte_array[0][0] = 8'hAA;
            byte_array[0][1] = 8'hBB;
            byte_array[1][0] = 8'hCC;
            byte_array[1][1] = 8'hDD;
            out_processed_valid = 1'b1;
            out_total_sum = internal_sum + byte_array[0][0] + byte_array[1][1];
        end else begin
            data_storage[0].count = 0;
            data_storage[0].data = 0;
            data_storage[0].packed_item.field_a = 0;
            data_storage[0].packed_item.field_b = 0;
            byte_array[0][0] = 0;
            out_total_sum = 0;
        end
    end
endmodule
module ClassProcessor (
    input int input_val_a,
    input int input_val_b,
    input logic select_op,
    output int output_result,
    output logic output_valid
);
    class MySimpleCalculator;
        int m_val_a;
        int m_val_b;
        function new(int a, int b);
            m_val_a = a;
            m_val_b = b;
        endfunction
        function int add_values();
            return m_val_a + m_val_b;
        endfunction
        function int multiply_values();
            return m_val_a * m_val_b;
        endfunction
        function int calculate_complex(int factor);
            return (m_val_a + m_val_b) * factor - m_val_a;
        endfunction
    endclass
    MySimpleCalculator calculator_h;
    always_comb begin
        int complex_intermediate; 
        output_result = 0;
        output_valid = 1'b0;
        calculator_h = new(input_val_a, input_val_b);
        if (select_op) begin
            output_result = calculator_h.multiply_values();
        end else begin
            output_result = calculator_h.add_values();
        end
        complex_intermediate = calculator_h.calculate_complex(5);
        output_result = output_result + complex_intermediate;
        output_valid = 1'b1;
    end
endmodule
module AdvancedDataTypesAndOps (
    input logic clk,
    input logic reset_n,
    input logic [7:0] data_in_q,
    input logic [7:0] addr_in_aa,
    output logic [7:0] data_out_q,
    output logic [7:0] data_out_aa,
    output logic [7:0] union_out
);
    typedef union {
        logic [15:0]  word;
        struct packed {
            logic [7:0]  byte_high;
            logic [7:0]  byte_low;
        } bytes;
    } my_union_t;
    my_union_t u_data;
    int dynamic_array[];
    logic [7:0] associative_array[*];
    logic [7:0] my_queue[$];
    int da_size;
    logic [15:0] concatenated_val;
    logic reduce_and, reduce_or;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            dynamic_array = new[0];
            associative_array.delete();
            my_queue.delete();
        end else begin
            if (my_queue.size() < 4) begin
                da_size = dynamic_array.size();
                dynamic_array = new[da_size + 1];
                dynamic_array[da_size] = data_in_q + 10;
            end else if (dynamic_array.size() > 0) begin
                dynamic_array = new[dynamic_array.size() - 1](dynamic_array);
            end
            my_queue.push_back(data_in_q);
            if (my_queue.size() > 5) begin
                void' (my_queue.pop_front());
            end
            if (addr_in_aa != 8'hFF) begin
                associative_array[addr_in_aa] = data_in_q;
            end
        end
    end
    always_comb begin
        data_out_q = 8'h00;
        data_out_aa = 8'h00;
        union_out = 8'h00;
        if (my_queue.size() > 0) begin
            data_out_q = my_queue[0];
        end
        if (associative_array.exists(addr_in_aa)) begin
            data_out_aa = associative_array[addr_in_aa];
        end
        u_data.word = {data_in_q, data_in_q + 1};
        union_out = u_data.bytes.byte_high + u_data.bytes.byte_low;
        concatenated_val = {u_data.bytes.byte_high[3:0], u_data.bytes.byte_low[7:4]};
        union_out = union_out + concatenated_val[7:0];
        reduce_and = &concatenated_val;
        reduce_or = |concatenated_val;
        union_out = union_out + (reduce_and ? 1 : 0) + (reduce_or ? 2 : 0);
    end
endmodule
