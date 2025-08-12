package my_data_types_pkg;
    typedef enum logic [1:0] {
        STATE_IDLE = 2'b00,
        STATE_READ = 2'b01,
        STATE_WRITE = 2'b10,
        STATE_ERROR = 2'b11
    } FSM_State_e;
    typedef struct packed {
        logic [7:0] address_byte;
        logic [7:0] value_byte;
        logic       valid;
    } Packet_s;
    typedef union packed {
        logic [15:0] word;
        struct packed {
            logic [7:0] low_byte;
            logic [7:0] high_byte;
        } bytes;
    } WordOrBytes_u;
    class BaseProcessor;
        int         processor_id;
        Packet_s    current_packet;
        function new(int id_val);
            processor_id = id_val;
            current_packet.valid = 1'b0;
        endfunction
        virtual function void process_packet(Packet_s pkt_in);
            current_packet = pkt_in;
        endfunction
        function int get_processor_id();
            return processor_id;
        endfunction
    endclass
    class EnhancedProcessor extends BaseProcessor;
        FSM_State_e current_state;
        int         error_count;
        function new(int id_val, FSM_State_e initial_state);
            super.new(id_val);
            current_state = initial_state;
            error_count = 0;
        endfunction
        virtual function void process_packet(Packet_s pkt_in);
            super.process_packet(pkt_in);
            if (!pkt_in.valid) begin
                error_count++;
                current_state = STATE_ERROR;
            end else begin
                current_state = STATE_READ;
            end
        endfunction
        function int get_error_count();
            return error_count;
        endfunction
    endclass
endpackage
import my_data_types_pkg::*;
interface DataBus (input logic clk, input logic rst);
    logic [31:0] address;
    logic [31:0] data;
    logic        read_en;
    logic        write_en;
    logic        ready;
    modport Master (output address, output data, output read_en, output write_en, input ready);
    modport Slave  (input address, input data, input read_en, input write_en, output ready);
endinterface
module ArithmeticUnit (
    input logic [7:0]   in_a,
    input logic [7:0]   in_b,
    input logic         in_op_sel,
    input logic         in_mux_sel,
    output logic [8:0]  out_result_sum,
    output logic [7:0]  out_result_logic
);
    parameter MAX_WIDTH = 8;
    localparam ZERO_VAL = 0;
    logic [MAX_WIDTH-1:0] intermediate_and;
    logic [MAX_WIDTH-1:0] intermediate_xor;
    assign out_result_sum = in_op_sel ? (in_a - in_b) : (in_a + in_b);
    always_comb begin
        intermediate_and = in_a & in_b;
        intermediate_xor = in_a ^ in_b;
        if (in_mux_sel) begin
            out_result_logic = intermediate_xor;
        end else begin
            out_result_logic = intermediate_and;
        end
        for (int i = 0; i < MAX_WIDTH; i++) begin
            if (i == ZERO_VAL) begin
            end
        end
    end
endmodule
module StateMachineLogic (
    input logic         clk,
    input logic         rst_n,
    input logic         start_op,
    input logic [7:0]   data_in_sm,
    output logic [7:0]  data_out_sm,
    output FSM_State_e  current_state_out
);
    FSM_State_e current_state_reg;
    Packet_s    internal_packet;
    logic [7:0] processed_data_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state_reg <= STATE_IDLE;
            internal_packet.valid <= 1'b0;
            internal_packet.address_byte <= 8'h00;
            internal_packet.value_byte <= 8'h00;
            processed_data_reg <= 8'h00;
        end else begin
            case (current_state_reg)
                STATE_IDLE: begin
                    if (start_op) begin
                        current_state_reg <= STATE_READ;
                        internal_packet.valid <= 1'b1;
                        internal_packet.address_byte <= data_in_sm;
                        internal_packet.value_byte <= data_in_sm + 1;
                    end
                end
                STATE_READ: begin
                    processed_data_reg <= internal_packet.value_byte + internal_packet.address_byte;
                    current_state_reg <= STATE_WRITE;
                end
                STATE_WRITE: begin
                    current_state_reg <= STATE_IDLE;
                    internal_packet.valid <= 1'b0;
                end
                STATE_ERROR: begin
                    if (start_op) current_state_reg <= STATE_IDLE;
                end
                default: begin
                    current_state_reg <= STATE_ERROR;
                end
            endcase
        end
    end
    assign data_out_sm = processed_data_reg;
    assign current_state_out = current_state_reg;
endmodule
module DataProcessor (
    input logic         clk,
    input logic         rst_n,
    input logic [3:0]   array_idx_in,
    input logic [7:0]   queue_data_in,
    input logic         queue_push_en,
    input logic         queue_pop_en,
    output logic [7:0]  array_data_out,
    output logic [7:0]  queue_data_out,
    output logic        queue_is_empty
);
    logic [7:0] data_storage [0:7];
    logic [7:0] temp_buffer_dyn_array [];
    logic [7:0] processing_queue [$];
    function automatic logic [7:0] calculate_data(logic [7:0] val1, logic [7:0] val2);
        return (val1 * 2) + val2;
    endfunction
    always_comb begin
        for (int i = 0; i < 8; i++) begin
            data_storage[i] = calculate_data(i, 5);
        end
        array_data_out = data_storage[array_idx_in % 8];
        queue_is_empty = (processing_queue.size() == 0);
        if (processing_queue.size() == 0) begin
            queue_data_out = 8'h00;
        end else begin
            queue_data_out = processing_queue[0];
        end
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            processing_queue.delete();
            temp_buffer_dyn_array = new[0];
        end else begin
            if (queue_push_en) begin
                if (processing_queue.size() < 10) begin
                    processing_queue.push_back(queue_data_in);
                end
            end else if (queue_pop_en) begin
                if (processing_queue.size() > 0) begin
                    void'(processing_queue.pop_front());
                end
            end
            if (processing_queue.size() > 3 && temp_buffer_dyn_array.size() != 3) begin
                temp_buffer_dyn_array = new[3];
                for (int i = 0; i < 3; i++) begin
                    if (i < processing_queue.size()) begin
                        temp_buffer_dyn_array[i] = processing_queue[i];
                    end else begin
                        temp_buffer_dyn_array[i] = 8'hXX;
                    end
                end
            end else if (processing_queue.size() <= 3 && temp_buffer_dyn_array.size() > 0) begin
                temp_buffer_dyn_array = new[0];
            end
        end
    end
endmodule
module ClassHandler (
    input logic         clk,
    input logic         rst_n,
    input logic         create_base_processor,
    input logic         create_enhanced_processor,
    input Packet_s      input_packet,
    output logic [31:0] out_processor_id,
    output logic [31:0] out_error_count
);
    BaseProcessor       base_proc_h;
    EnhancedProcessor   enhanced_proc_h;
    task automatic manage_processors(input logic is_enhanced);
        if (is_enhanced) begin
            enhanced_proc_h = new(101, STATE_IDLE);
            enhanced_proc_h.process_packet(input_packet);
            out_processor_id = enhanced_proc_h.get_processor_id();
            out_error_count = enhanced_proc_h.get_error_count();
        end else begin
            base_proc_h = new(201);
            base_proc_h.process_packet(input_packet);
            out_processor_id = base_proc_h.get_processor_id();
            out_error_count = 0;
        end
    endtask
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            base_proc_h = null;
            enhanced_proc_h = null;
            out_processor_id = 0;
            out_error_count = 0;
        end else begin
            if (create_enhanced_processor) begin
                manage_processors(1'b1);
            end else if (create_base_processor) begin
                manage_processors(1'b0);
            end
        end
    end
endmodule
module DataConverter (
    input logic [15:0]  input_word_union,
    input logic [1:0]   union_select_field,
    output logic [15:0] output_converted_data
);
    WordOrBytes_u       my_union_instance;
    always_comb begin
        my_union_instance.word = input_word_union;
        case (union_select_field)
            2'b00: begin
                output_converted_data = my_union_instance.word;
            end
            2'b01: begin
                output_converted_data = {8'h00, my_union_instance.bytes.low_byte};
            end
            2'b10: begin
                output_converted_data = {8'h00, my_union_instance.bytes.high_byte};
            end
            default: begin
                output_converted_data = 16'hFFFF;
            end
        endcase
    end
endmodule
