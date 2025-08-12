module BasicLogic(
    input logic        clk,
    input logic        rst_n,
    input logic [7:0]  data_in,
    output logic [7:0] data_out_comb,
    output logic [7:0] data_out_seq,
    output logic [15:0] param_calc_out
);
    parameter P_OFFSET = 8;
    localparam LP_MASK = 16'hFF00;
    logic [7:0] reg_data;
    assign data_out_comb = data_in + P_OFFSET;
    always_comb begin
        param_calc_out = (data_in << P_OFFSET) | (LP_MASK & 16'h00FF);
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            reg_data <= 8'b0;
        end else begin
            reg_data <= data_in;
        end
    end
    assign data_out_seq = reg_data;
endmodule
module StructuredTypes(
    input logic         valid_i,
    input logic [1:0]   op_code_i,
    input logic [7:0]   value_i,
    output logic [15:0] result_o,
    output logic        error_o
);
    typedef enum logic [1:0] {
        OP_ADD = 2'b00,
        OP_SUB = 2'b01,
        OP_MUL = 2'b10,
        OP_DIV = 2'b11
    } operation_e;
    typedef struct packed {
        logic [7:0] operand1;
        logic [7:0] operand2;
        operation_e op;
    } math_packet_t;
    math_packet_t current_packet;
    logic [7:0]   lookup_rom [4];
    always_comb begin
        lookup_rom[0] = 8'd10;
        lookup_rom[1] = 8'd20;
        lookup_rom[2] = 8'd30;
        lookup_rom[3] = 8'd40;
    end
    logic [15:0] internal_result;
    logic        internal_error;
    always_comb begin
        internal_result = 16'b0;
        internal_error = 1'b0;
        current_packet.operand1 = value_i;
        current_packet.operand2 = lookup_rom[op_code_i[1:0]];
        current_packet.op       = operation_e'(op_code_i);
        if (valid_i) begin
            case (current_packet.op)
                OP_ADD: internal_result = current_packet.operand1 + current_packet.operand2;
                OP_SUB: internal_result = current_packet.operand1 - current_packet.operand2;
                OP_MUL: internal_result = current_packet.operand1 * current_packet.operand2;
                OP_DIV: begin
                    if (current_packet.operand2 != 8'b0) begin
                        internal_result = current_packet.operand1 / current_packet.operand2;
                    end else begin
                        internal_error = 1'b1;
                    end
                end
                default: internal_error = 1'b1;
            endcase
        end
    end
    assign result_o = internal_result;
    assign error_o = internal_error;
endmodule
module TaskFunctionModule(
    input logic [7:0] input_a,
    input logic [7:0] input_b,
    input logic       op_select,
    output logic [8:0] sum_sub_out,
    output logic [15:0] multi_out
);
    function automatic logic [15:0] multiplier(input logic [7:0] a, input logic [7:0] b);
        return a * b;
    endfunction
    task automatic calculate_sum_sub(input logic [7:0] a, input logic [7:0] b, input logic select, output logic [8:0] result);
        if (select == 1'b0) begin
            result = a + b;
        end else begin
            result = a - b;
        end
    endtask
    logic [8:0] temp_sum_sub;
    always_comb begin
        calculate_sum_sub(input_a, input_b, op_select, temp_sum_sub);
        sum_sub_out = temp_sum_sub;
        multi_out = multiplier(input_a, input_b);
    end
endmodule
interface MyBus(input logic clk, input logic rst_n);
    logic [31:0] address;
    logic [31:0] data_in;
    logic [31:0] data_out;
    logic        read_en;
    logic        write_en;
    logic        ack;
endinterface
module InterfaceUser(
    input logic clk_i,
    input logic rst_n_i,
    input logic [31:0] addr_in,
    input logic [31:0] data_in_i,
    input logic        read_req_i,
    output logic [31:0] data_out_o,
    output logic        ack_o
);
    MyBus bus_inst(.clk(clk_i), .rst_n(rst_n_i));
    assign bus_inst.address  = addr_in;
    assign bus_inst.data_in  = data_in_i;
    assign bus_inst.read_en  = read_req_i;
    assign bus_inst.write_en = !read_req_i;
    logic [31:0] memory_array [1024];
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            for (int i = 0; i < 1024; i++) begin
                memory_array[i] <= 0;
            end
            bus_inst.ack <= 1'b0;
        end else begin
            if (bus_inst.write_en) begin
                memory_array[bus_inst.address[9:0]] <= bus_inst.data_in;
                bus_inst.ack <= 1'b1;
            end else if (bus_inst.read_en) begin
                bus_inst.data_out <= memory_array[bus_inst.address[9:0]];
                bus_inst.ack <= 1'b1;
            end else begin
                bus_inst.ack <= 1'b0;
            end
        end
    end
    assign data_out_o = bus_inst.data_out;
    assign ack_o      = bus_inst.ack;
endmodule
module ClassExample(
    input logic        clk,
    input logic        rst_n,
    input logic [7:0]  input_val,
    input logic        trigger_calc,
    output logic [15:0] class_result_out,
    output logic [7:0] array_sum_out
);
    class DataProcessor;
        rand int unsigned my_data_array[];
        int unsigned      result_val;
        function new();
            my_data_array = new[5];
            foreach (my_data_array[i]) begin
                my_data_array[i] = i * 10;
            end
            result_val = 0;
        endfunction
        function void process_data(int unsigned input_data);
            int sum = 0;
            int current_size = my_data_array.size();
            my_data_array = new[current_size + 1](my_data_array);
            my_data_array[current_size] = input_data;
            if (my_data_array.size() > 10) begin
                int new_size = my_data_array.size() - 1;
                int unsigned temp_arr_shift[];
                temp_arr_shift = new[new_size];
                for (int i = 0; i < new_size; i++) begin
                    temp_arr_shift[i] = my_data_array[i+1];
                end
                my_data_array = temp_arr_shift;
            end
            foreach (my_data_array[i]) begin
                sum += my_data_array[i];
            end
            result_val = sum;
        endfunction
        function int unsigned get_result();
            return result_val;
        endfunction
        function int unsigned get_array_sum();
            int sum = 0;
            foreach (my_data_array[i]) begin
                sum += my_data_array[i];
            end
            return sum;
        endfunction
    endclass
    DataProcessor my_processor;
    logic [15:0] current_class_result;
    logic [7:0] current_array_sum;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            my_processor = new();
            current_class_result = 16'b0;
            current_array_sum = 8'b0;
        end else if (trigger_calc) begin
            if (my_processor == null) begin
                my_processor = new();
            end
            my_processor.process_data(input_val);
            current_class_result = my_processor.get_result();
            current_array_sum = my_processor.get_array_sum();
        end
    end
    assign class_result_out = current_class_result;
    assign array_sum_out = current_array_sum;
endmodule
module GenerateExample(
    input logic [1:0] select_mode,
    input logic [7:0] data_in_gen,
    output logic [7:0] data_out_gen
);
    parameter NUM_ADDERS = 2;
    logic [7:0] adder_outputs [NUM_ADDERS-1:0];
    logic [7:0] multiplier_output;
    logic [7:0] passthrough_output;
    generate
        if (NUM_ADDERS > 1) begin : MULTIPLE_ADDERS
            for (genvar i = 0; i < NUM_ADDERS; i++) begin : ADDER_CHAIN
                if (i == 0) begin
                    assign adder_outputs[i] = data_in_gen + i;
                end else begin
                    assign adder_outputs[i] = adder_outputs[i-1] + i;
                end
            end
        end else begin : SINGLE_ADDER
            assign adder_outputs[0] = data_in_gen + 1;
        end
    endgenerate
    always_comb begin
        multiplier_output = data_in_gen * 2;
        passthrough_output = data_in_gen;
        case (select_mode)
            2'b00: data_out_gen = adder_outputs[NUM_ADDERS-1];
            2'b01: data_out_gen = multiplier_output;
            2'b10: data_out_gen = passthrough_output;
            default: data_out_gen = 8'b0;
        endcase
    end
endmodule
module AssertionExample(
    input logic        clk_assert,
    input logic        rst_n_assert,
    input logic        enable_assert,
    input logic [3:0]  value_assert,
    output logic       error_flag_out
);
    always_comb begin
        if (enable_assert) begin
            assert (value_assert >= 0 && value_assert <= 10);
        end
    end
    assert property (@(posedge clk_assert) enable_assert |-> value_assert < 8);
    logic internal_error_flag;
    always_comb begin
        internal_error_flag = (value_assert > 10);
    end
    assign error_flag_out = internal_error_flag;
endmodule
