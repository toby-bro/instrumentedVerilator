package MyCommonTypes;
    typedef struct packed {
        logic [15:0] timestamp;
        logic [7:0]  payload_len;
        logic [31:0] payload_data;
    } DataPacket_t;
    typedef union packed {
        logic [31:0] raw_val;
        struct packed {
            logic [15:0] crc;
            logic [15:0] counter;
        } parsed_val;
    } ResultData_t;
    typedef enum logic [1:0] {
        FSM_IDLE,
        FSM_STEP1,
        FSM_STEP2,
        FSM_DONE
    } FSM_State_t;
endpackage
class SimpleCalculator;
    logic [15:0] internal_data;
    function new(input logic [15:0] initial_val);
        internal_data = initial_val;
    endfunction
    function logic [15:0] add_one();
        return internal_data + 1;
    endfunction
    function logic [15:0] multiply_by_two();
        return internal_data << 1;
    endfunction
    function logic [15:0] negate_val();
        return ~internal_data;
    endfunction
endclass
module ArithmeticLogicUnit #(
    parameter DATA_WIDTH = 8
) (
    input logic [DATA_WIDTH-1:0] in_a,
    input logic [DATA_WIDTH-1:0] in_b,
    input logic [1:0] op_sel,
    output logic [DATA_WIDTH-1:0] out_result
);
    logic [DATA_WIDTH-1:0] temp_result;
    always_comb begin
        case (op_sel)
            2'b00: temp_result = in_a + in_b;
            2'b01: temp_result = in_a - in_b;
            2'b10: temp_result = in_a & in_b;
            2'b11: temp_result = in_a | in_b;
            default: temp_result = '0;
        endcase
        out_result = temp_result;
    end
endmodule
module SequencerWithEnum (
    input logic clk,
    input logic reset_n,
    input logic start_seq,
    input logic [7:0] data_in,
    output logic [7:0] data_out,
    output logic seq_done
);
    import MyCommonTypes::*;
    FSM_State_t current_state, next_state;
    logic [7:0] internal_data_reg;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            current_state <= FSM_IDLE;
            internal_data_reg <= '0;
        end else begin
            current_state <= next_state;
            if (current_state == FSM_STEP1) begin
                internal_data_reg <= data_in + 1;
            end else if (current_state == FSM_STEP2) begin
                internal_data_reg <= internal_data_reg * 2;
            end
        end
    end
    always_comb begin
        next_state = current_state;
        data_out = internal_data_reg;
        seq_done = 1'b0;
        case (current_state)
            FSM_IDLE: begin
                if (start_seq) begin
                    next_state = FSM_STEP1;
                end
            end
            FSM_STEP1: begin
                next_state = FSM_STEP2;
            end
            FSM_STEP2: begin
                next_state = FSM_DONE;
            end
            FSM_DONE: begin
                seq_done = 1'b1;
                if (!start_seq) begin
                    next_state = FSM_IDLE;
                end
            end
            default: begin
                next_state = FSM_IDLE;
            end
        endcase
    end
endmodule
module ComplexDataProcessor (
    input MyCommonTypes::DataPacket_t input_packet,
    input logic [3:0] config_id,
    output MyCommonTypes::ResultData_t output_result
);
    import MyCommonTypes::*;
    localparam MAX_ENTRIES = 4;
    DataPacket_t packet_buffer [MAX_ENTRIES];
    logic [31:0] temp_processed_val;
    always_comb begin
        temp_processed_val = '0;
        output_result.raw_val = '0;
        for (int i=0; i < MAX_ENTRIES; i++) begin
            packet_buffer[i].timestamp = input_packet.timestamp + i;
            packet_buffer[i].payload_len = input_packet.payload_len + i;
            packet_buffer[i].payload_data = input_packet.payload_data + i;
        end
        case (config_id)
            4'd0: begin
                logic [7:0] total_len;
                total_len = '0;
                for (int i=0; i < MAX_ENTRIES; i++) begin
                    total_len += packet_buffer[i].payload_len;
                end
                temp_processed_val = total_len;
            end
            4'd1: begin
                temp_processed_val = input_packet.payload_data[15:0];
            end
            4'd2: begin
                logic [31:0] reordered_data;
                reordered_data = {<<8{input_packet.payload_data}};
                temp_processed_val = reordered_data;
            end
            default: begin
                temp_processed_val = input_packet.payload_data ^ input_packet.timestamp;
            end
        endcase
        output_result.raw_val = temp_processed_val;
        output_result.parsed_val.crc = temp_processed_val[15:0] ^ temp_processed_val[31:16];
        output_result.parsed_val.counter = temp_processed_val[15:0];
    end
endmodule
module ObjectOrientedProcessor (
    input logic [15:0] in_value,
    input logic [1:0] operation_code,
    output logic [15:0] out_result
);
    SimpleCalculator calc_obj;
    logic [15:0] temp_calc_result;
    always_comb begin
        calc_obj = new(in_value);
        temp_calc_result = '0;
        case (operation_code)
            2'b00: temp_calc_result = calc_obj.add_one();
            2'b01: temp_calc_result = calc_obj.multiply_by_two();
            2'b10: temp_calc_result = calc_obj.negate_val();
            2'b11: temp_calc_result = calc_obj.internal_data;
            default: temp_calc_result = '0;
        endcase
        out_result = temp_calc_result;
    end
endmodule
module ConfigurableArrayProcessor #(
    parameter NUM_ARRAYS = 2,
    parameter ARRAY_SIZE = 8
) (
    input logic [($clog2(NUM_ARRAYS > 1 ? NUM_ARRAYS : 2))-1:0] cfg_index,
    input logic [7:0] data_value,
    output logic [15:0] array_sum,
    output logic [7:0] selected_value
);
    logic [7:0] data_storage [NUM_ARRAYS-1:0][ARRAY_SIZE-1:0];
    always_comb begin
        if (cfg_index < ARRAY_SIZE) begin
            data_storage[0][cfg_index] = data_value;
        end
        array_sum = '0;
        for (int j = 0; j < ARRAY_SIZE; j++) begin
            if (cfg_index < NUM_ARRAYS) begin
                array_sum += data_storage[cfg_index][j];
            end
        end
    end
    always_comb begin
        if (cfg_index < NUM_ARRAYS && ARRAY_SIZE > 0) begin
            selected_value = data_storage[cfg_index][0];
        end else begin
            selected_value = '0;
        end
    end
    genvar i;
    generate
        if (ARRAY_SIZE > 4) begin : large_array_feature
            logic [7:0] sum_first_four;
            always_comb begin
                sum_first_four = data_storage[0][0] + data_storage[0][1] +
                                 data_storage[0][2] + data_storage[0][3];
            end
        end
        for (i = 0; i < NUM_ARRAYS; i++) begin : per_array_constant
            localparam SOME_OFFSET = i * 2;
        end
    endgenerate
endmodule
module DynamicArrayProcessor (
    input logic [7:0] in_data_item,
    input logic [1:0] operation_mode,
    output logic [15:0] total_sum,
    output int current_collection_size
);
    int my_queue[$];
    int my_assoc_array[string];
    always_comb begin
        total_sum = '0;
        current_collection_size = 0;
        case (operation_mode)
            2'b00: begin
                my_queue.push_back(in_data_item);
                foreach (my_queue[i]) begin
                    total_sum += my_queue[i];
                end
                current_collection_size = my_queue.size();
                if (my_queue.size() > 10) begin
                    my_queue.pop_front();
                end
            end
            2'b01: begin
                string key_str;
                string current_key;
                key_str = $sformatf("item_%0d", in_data_item);
                my_assoc_array[key_str] = in_data_item * 2;
                if (my_assoc_array.first(current_key)) begin
                    do begin
                        total_sum += my_assoc_array[current_key];
                    end while (my_assoc_array.next(current_key));
                end
                current_collection_size = my_assoc_array.num();
            end
            default: begin
            end
        endcase
    end
endmodule
module RealNumberProcessor (
    input real in_real_val,
    input logic [1:0] op_type,
    output real out_real_val
);
    real temp_real;
    always_comb begin
        case (op_type)
            2'b00: temp_real = in_real_val * 2.5;
            2'b01: temp_real = in_real_val + 10.0;
            2'b10: temp_real = in_real_val / 3.0;
            2'b11: begin
                if (in_real_val >= 0.0)
                    temp_real = $sqrt(in_real_val);
                else
                    temp_real = 0.0;
            end
            default: temp_real = 0.0;
        endcase
        out_real_val = temp_real;
    end
endmodule
