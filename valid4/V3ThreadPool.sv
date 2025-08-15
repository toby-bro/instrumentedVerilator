module Complex_Logic_Arrays (
    input  logic [31:0] in_data_a,
    input  logic [31:0] in_data_b,
    output logic [31:0] out_result
);
    typedef enum logic [1:0] { OP_ADD, OP_SUB, OP_MUL, OP_DIV } OperationType;
    logic [7:0]  byte_array [4];
    logic [3:0][7:0] packed_byte_array;
    logic [31:0] intermediate_sum;
    logic [31:0] intermediate_product;
    logic [31:0] final_calc;
    OperationType current_op;
    assign packed_byte_array[0] = in_data_a[7:0];
    assign packed_byte_array[1] = in_data_a[15:8];
    assign packed_byte_array[2] = in_data_a[23:16];
    assign packed_byte_array[3] = in_data_a[31:24];
    always_comb begin
        for (int i = 0; i < 4; i++) begin
            byte_array[i] = in_data_b[i*8 +: 8];
        end
    end
    always_comb begin
        intermediate_sum = 0;
        for (int i = 0; i < 4; i++) begin
            intermediate_sum += packed_byte_array[i];
        end
    end
    always_comb begin
        intermediate_product = 1;
        intermediate_product *= (byte_array[0] + byte_array[1]);
        intermediate_product *= (byte_array[2] - byte_array[3]);
    end
    always_comb begin
        if (in_data_a[0] && in_data_b[0]) begin
            current_op = OP_ADD;
        end else if (in_data_a[1] || in_data_b[1]) begin
            current_op = OP_SUB;
        end else begin
            current_op = OP_MUL;
        end
        case (current_op)
            OP_ADD: final_calc = intermediate_sum + intermediate_product;
            OP_SUB: final_calc = intermediate_sum - intermediate_product;
            OP_MUL: final_calc = intermediate_sum * intermediate_product;
            OP_DIV: final_calc = (intermediate_product == 0) ? 0 : intermediate_sum / intermediate_product;
            default: final_calc = 0;
        endcase
    end
    assign out_result = final_calc;
endmodule
module Object_Oriented_Behavior (
    input  logic clk,
    input  logic rst_n,
    input  logic [7:0] in_val_a,
    input  logic [7:0] in_val_b,
    output logic [15:0] out_calc_val
);
    class MyDataProcessor;
        int m_val1;
        int m_val2;
        int m_internal_counter;
        function new(int val_in1, int val_in2);
            m_val1 = val_in1;
            m_val2 = val_in2;
            m_internal_counter = 0;
        endfunction
        function automatic int calculate_sum_and_increment();
            m_internal_counter++;
            return m_val1 + m_val2 + m_internal_counter;
        endfunction
        function automatic int multiply_and_update(ref int update_val);
            int product = m_val1 * m_val2;
            update_val = product;
            return product;
        endfunction
        function automatic void set_val1(int new_val);
            this.m_val1 = new_val;
        endfunction
        function automatic int get_internal_counter();
            return m_internal_counter;
        endfunction
    endclass : MyDataProcessor
    MyDataProcessor dp_obj_1;
    MyDataProcessor dp_obj_2;
    logic [15:0] current_sum_q;
    logic [15:0] current_product_q;
    int temp_update_val_q;
    logic [7:0]  counter_val_q;
    logic [7:0] in_val_a_q;
    logic [7:0] in_val_b_q;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            in_val_a_q <= 0;
            in_val_b_q <= 0;
        end else begin
            in_val_a_q <= in_val_a;
            in_val_b_q <= in_val_b;
        end
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            dp_obj_1 <= new(in_val_a_q, in_val_b_q);
            dp_obj_2 <= new(in_val_b_q, in_val_a_q);
            current_sum_q <= 0;
            current_product_q <= 0;
            temp_update_val_q <= 0;
            counter_val_q <= 0;
        end else begin
            if (dp_obj_1 != null && dp_obj_2 != null) begin
                int next_sum;
                int next_product;
                int next_update_val;
                int next_counter;
                dp_obj_1.set_val1(in_val_a_q + 5);
                next_sum = dp_obj_1.calculate_sum_and_increment();
                next_update_val = 0;
                next_product = dp_obj_2.multiply_and_update(next_update_val);
                next_counter = dp_obj_1.get_internal_counter();
                current_sum_q <= next_sum;
                current_product_q <= next_product;
                temp_update_val_q <= next_update_val;
                counter_val_q <= next_counter;
            end
        end
    end
    assign out_calc_val = current_sum_q + current_product_q + temp_update_val_q + counter_val_q;
endmodule
module FSM_with_Shared_State (
    input  logic clk,
    input  logic rst_n,
    input  logic enable_input,
    output logic [2:0] current_state_out
);
    typedef enum logic [2:0] {
        STATE_IDLE,
        STATE_WAIT,
        STATE_PROCESS_A,
        STATE_PROCESS_B,
        STATE_DONE
    } FsmState;
    FsmState current_state, next_state;
    logic [7:0] shared_counter;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state <= STATE_IDLE;
            shared_counter <= 0;
        end else begin
            current_state <= next_state;
        end
    end
    always_comb begin
        next_state = current_state;
        case (current_state)
            STATE_IDLE: begin
                if (enable_input) begin
                    next_state = STATE_WAIT;
                end
            end
            STATE_WAIT: begin
                if (shared_counter >= 5) begin
                    next_state = STATE_PROCESS_A;
                end
            end
            STATE_PROCESS_A: begin
                if (shared_counter[0]) begin
                    next_state = STATE_PROCESS_B;
                end else begin
                    next_state = STATE_DONE;
                end
            end
            STATE_PROCESS_B: begin
                next_state = STATE_DONE;
            end
            STATE_DONE: begin
                if (!enable_input) begin
                    next_state = STATE_IDLE;
                end
            end
            default: next_state = STATE_IDLE;
        endcase
    end
    always_ff @(posedge clk) begin
        if (current_state == STATE_IDLE && enable_input) begin
            shared_counter <= shared_counter + 1;
        end else if (current_state == STATE_PROCESS_A) begin
            shared_counter <= shared_counter + 2;
        end else if (current_state == STATE_PROCESS_B) begin
            shared_counter <= shared_counter + 4;
        end
    end
    assign current_state_out = current_state;
endmodule
module Task_Function_Hierarchy (
    input  logic [15:0] op_a,
    input  logic [15:0] op_b,
    output logic [31:0] final_res
);
    logic [31:0] temp_accum;
    function automatic int add_func(int val1, int val2);
        return val1 + val2;
    endfunction
    task automatic process_values (input int in1, input int in2, output int out_sum, output int out_product);
        int local_temp_sum;
        local_temp_sum = add_func(in1, in2);
        out_sum = local_temp_sum;
        out_product = in1 * in2;
    endtask
    task automatic complex_operation (input int val_x, input int val_y, output int result_out);
        int p_sum;
        int p_prod;
        process_values(val_x, val_y, p_sum, p_prod);
        result_out = p_sum + (p_prod >>> 2);
        if (p_sum > 100) begin
            result_out = result_out * 2;
        end
    endtask
    always_comb begin
        int res_x, res_y;
        temp_accum = 0;
        complex_operation(op_a, op_b, res_x);
        temp_accum = res_x;
        complex_operation(op_b, op_a, res_y);
        temp_accum = temp_accum + res_y;
        temp_accum = add_func(temp_accum, (op_a ^ op_b));
    end
    assign final_res = temp_accum;
endmodule
interface SimpleBus (input logic clk, input logic rst);
    logic [7:0] data;
    logic       valid;
    logic       ready;
    modport Master (output data, output valid, input ready, output clk, output rst);
    modport Slave  (input data, input valid, output ready, input clk, input rst);
endinterface
module Interface_Master (
    input  logic clk_i,
    input  logic rst_i,
    input  logic [7:0] input_data,
    output logic [7:0] data_out_port
);
    SimpleBus bus_itf (.clk(clk_i), .rst(rst_i));
    always_comb begin
        bus_itf.Master.data = input_data;
        bus_itf.Master.valid = (input_data != 0);
    end
    logic [7:0] slave_feedback;
    assign slave_feedback = bus_itf.Slave.data;
    assign data_out_port = slave_feedback;
    logic [7:0] slave_dummy_output_connection;
    Interface_Slave u_slave (
        .clk_s(clk_i),
        .rst_s(rst_i),
        .bus_port(bus_itf),
        .dummy_out(slave_dummy_output_connection)
    );
endmodule
module Interface_Slave (
    input  logic clk_s,
    input  logic rst_s,
    output logic [7:0] dummy_out,
    SimpleBus.Slave bus_port
);
    logic [7:0] internal_data_reg;
    always_ff @(posedge clk_s or posedge rst_s) begin
        if (rst_s) begin
            internal_data_reg <= 0;
            bus_port.ready <= 0;
        end else begin
            bus_port.ready <= bus_port.valid;
            if (bus_port.valid && bus_port.ready) begin
                internal_data_reg <= bus_port.data + 1;
            end
        end
    end
    assign dummy_out = internal_data_reg;
endmodule
module Generic_Parameterized_Module #(
    parameter DATA_WIDTH = 8,
    parameter NUM_REGISTERS = 4
) (
    input  logic [DATA_WIDTH-1:0] data_in_p,
    output logic [DATA_WIDTH-1:0] data_out_p
);
    localparam TOTAL_BITS = DATA_WIDTH * NUM_REGISTERS;
    logic [DATA_WIDTH-1:0] registers [NUM_REGISTERS-1:0];
    logic [DATA_WIDTH-1:0] piped_output;
    always_comb begin
        registers[0] = data_in_p;
        for (int i = 1; i < NUM_REGISTERS; i++) begin
            registers[i] = registers[i-1] + 1;
        end
        piped_output = registers[NUM_REGISTERS-1];
    end
    genvar i;
    generate
        for (i = 0; i < NUM_REGISTERS; i++) begin : gen_logic_per_reg
            if (i % 2 == 0) begin : even_reg_check
            end else begin : odd_reg_check
            end
        end
    endgenerate
    assign data_out_p = piped_output;
endmodule
