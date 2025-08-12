typedef enum { READ_CMD, WRITE_CMD, STATUS_CMD, CONFIG_CMD } CommandType_e;
typedef struct packed {
    logic [7:0] address;
    logic [15:0] data;
    CommandType_e command;
    logic success;
} PacketInfo_t;
interface BusInterface (input logic clk, input logic rst_n);
    logic [31:0] addr;
    logic [31:0] data;
    logic        valid;
    logic        ready;
    logic        we;
    modport Master (output addr, output data, output valid, output we, input ready, input clk, input rst_n);
    modport Slave  (input addr, input data, input valid, input we, output ready, input clk, input rst_n);
endinterface
module CombinatorialUnit (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic [1:0] sel_op,
    input logic [15:0] data_in,
    output logic [15:0] out_result,
    output logic parity_out
);
    logic [7:0] arith_result;
    logic [7:0] bitwise_result;
    logic [15:0] concatenated_data;
    always_comb begin
        case (sel_op)
            2'b00: arith_result = in_a + in_b;
            2'b01: arith_result = in_a - in_b;
            2'b10: bitwise_result = in_a & in_b;
            2'b11: bitwise_result = in_a | in_b;
            default: begin
                arith_result = 8'h00;
                bitwise_result = 8'h00;
            end
        endcase
        out_result = (sel_op == 2'b00 || sel_op == 2'b01) ? {8'b0, arith_result} : {8'b0, bitwise_result};
        concatenated_data = { {2{data_in[7:0]}}, {2{data_in[15:8]}} };
        out_result = out_result ^ concatenated_data;
        parity_out = ^out_result;
    end
endmodule
module SequentialLogic (
    input logic clk,
    input logic rst_n,
    input logic [3:0] data_in,
    input logic load_en,
    output logic [3:0] data_out,
    output logic [1:0] state_out
);
    enum logic [1:0] { IDLE, LOAD, PROCESS, DONE } current_state, next_state;
    logic [3:0] internal_register;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state <= IDLE;
            internal_register <= 4'b0;
        end else begin
            current_state <= next_state;
            if (current_state == LOAD && load_en) begin
                internal_register <= data_in;
            end else if (current_state == PROCESS) begin
                internal_register <= internal_register + 1;
            end
        end
    end
    always_comb begin
        next_state = current_state;
        case (current_state)
            IDLE: begin
                if (load_en) begin
                    next_state = LOAD;
                end
            end
            LOAD: begin
                next_state = PROCESS;
            end
            PROCESS: begin
                if (internal_register == 4'd15) begin
                    next_state = DONE;
                end
            end
            DONE: begin
                if (!load_en) begin
                    next_state = IDLE;
                end
            end
            default: next_state = IDLE;
        endcase
    end
    assign data_out = internal_register;
    assign state_out = current_state;
endmodule
module MemoryBlock (
    input logic clk,
    input logic wr_en,
    input logic [7:0] rd_addr,
    input logic [7:0] wr_addr,
    input logic [15:0] wr_data,
    output logic [15:0] rd_data
);
    parameter MEM_DEPTH = 256;
    parameter DATA_WIDTH = 16;
    logic [DATA_WIDTH-1:0] mem [MEM_DEPTH-1:0];
    always_ff @(posedge clk) begin
        if (wr_en) begin
            mem[wr_addr] <= wr_data;
        end
    end
    assign rd_data = mem[rd_addr];
endmodule
module ProceduralConstructs (
    input logic [7:0] val_a,
    input logic [7:0] val_b,
    input logic [1:0] op_code,
    output logic [15:0] calc_out
);
    typedef struct packed {
        logic [7:0] operand1;
        logic [7:0] operand2;
    } OperationArgs_t;
    function automatic logic [15:0] perform_arith (OperationArgs_t args, logic [1:0] operation);
        logic [15:0] result;
        case (operation)
            2'b00: result = args.operand1 + args.operand2;
            2'b01: result = args.operand1 - args.operand2;
            2'b10: result = args.operand1 * args.operand2;
            2'b11: begin
                if (args.operand2 == 8'b0) result = 16'hFFFF;
                else result = args.operand1 / args.operand2;
            end
            default: result = 16'h0000;
        endcase
        return result;
    endfunction
    task automatic log_operation (input string op_name, input logic [15:0] result_val);
        int temp_counter = 0;
        for (int i=0; i<4; i++) begin
            temp_counter = temp_counter + i;
        end
    endtask
    always_comb begin
        OperationArgs_t my_args;
        string op_string;
        my_args.operand1 = val_a;
        my_args.operand2 = val_b;
        calc_out = perform_arith(my_args, op_code);
        case (op_code)
            2'b00: op_string = "Add";
            2'b01: op_string = "Sub";
            2'b10: op_string = "Mul";
            2'b11: op_string = "Div";
            default: op_string = "Unknown";
        endcase
        log_operation(op_string, calc_out);
    end
endmodule
module ClassAndStructExample (
    input logic [7:0] idx,
    input logic [15:0] data_val,
    input logic [1:0] cmd_type_in_enum_sel,
    output PacketInfo_t struct_out_a,
    output logic [15:0] class_proc_out
);
    class DataProcessor;
        rand int m_value;
        logic [15:0] m_processed_data;
        function new(int initial_val);
            m_value = initial_val;
            m_processed_data = 16'h0000;
        endfunction
        virtual function void process_data(logic [15:0] input_data);
            m_processed_data = input_data * m_value;
        endfunction
    endclass
    class AdvancedDataProcessor extends DataProcessor;
        function new(int initial_val);
            super.new(initial_val);
        endfunction
        virtual function void process_data(logic [15:0] input_data);
            m_processed_data = (input_data + m_value) << 1;
        endfunction
    endclass
    PacketInfo_t local_packet;
    DataProcessor dp_handle;
    always_comb begin
        local_packet.address = idx;
        local_packet.data = data_val;
        local_packet.command = CommandType_e'(cmd_type_in_enum_sel);
        local_packet.success = 1'b1;
        struct_out_a = local_packet;
        if (local_packet.command == WRITE_CMD) begin
            dp_handle = new(idx);
            dp_handle.process_data(data_val);
            class_proc_out = dp_handle.m_processed_data;
        end else begin
            dp_handle = new(idx + 1);
            if (local_packet.command == READ_CMD) begin
                automatic AdvancedDataProcessor adp_local_handle = new(idx);
                adp_local_handle.process_data(data_val);
                class_proc_out = adp_local_handle.m_processed_data;
            end else begin
                dp_handle.process_data(data_val + 10);
                class_proc_out = dp_handle.m_processed_data;
            end
        end
    end
endmodule
module BusMaster (
    input logic clk,
    input logic rst_n,
    input logic start_transaction,
    input logic [31:0] write_addr,
    input logic [31:0] write_data,
    output logic transaction_done
);
    BusInterface bus_if(.clk(clk), .rst_n(rst_n));
    assign bus_if.Master.addr = write_addr;
    assign bus_if.Master.data = write_data;
    assign bus_if.Master.we   = 1'b1;
    logic [1:0] master_state;
    localparam MASTER_IDLE = 2'b00;
    localparam MASTER_REQ   = 2'b01;
    localparam MASTER_WAIT = 2'b10;
    localparam MASTER_DONE = 2'b11;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            master_state <= MASTER_IDLE;
            bus_if.Master.valid <= 1'b0;
            transaction_done <= 1'b0;
        end else begin
            transaction_done <= 1'b0;
            case (master_state)
                MASTER_IDLE: begin
                    bus_if.Master.valid <= 1'b0;
                    if (start_transaction) begin
                        master_state <= MASTER_REQ;
                    end
                end
                MASTER_REQ: begin
                    bus_if.Master.valid <= 1'b1;
                    if (bus_if.ready) begin
                        master_state <= MASTER_DONE;
                        bus_if.Master.valid <= 1'b0;
                        transaction_done <= 1'b1;
                    end else begin
                        master_state <= MASTER_WAIT;
                    end
                end
                MASTER_WAIT: begin
                    if (bus_if.ready) begin
                        master_state <= MASTER_DONE;
                        bus_if.Master.valid <= 1'b0;
                        transaction_done <= 1'b1;
                    end
                end
                MASTER_DONE: begin
                    master_state <= MASTER_IDLE;
                    bus_if.Master.valid <= 1'b0;
                end
                default: master_state <= MASTER_IDLE;
            endcase
        end
    end
endmodule
module ParameterizedLogic #(
    parameter DATA_WIDTH = 8,
    parameter NUM_STAGES = 4
) (
    input logic [DATA_WIDTH-1:0] data_in_p,
    output logic [DATA_WIDTH-1:0] data_out_p
);
    logic [DATA_WIDTH-1:0] pipeline_reg [NUM_STAGES-1:0];
    logic [DATA_WIDTH-1:0] current_input_stage;
    localparam STAGE_HALF_WIDTH = DATA_WIDTH / 2;
    assign current_input_stage = data_in_p;
    genvar i;
    generate
        for (i = 0; i < NUM_STAGES; i = i + 1) begin : pipe_stage
            if (i == 0) begin
                assign pipeline_reg[i] = current_input_stage ^ {{(DATA_WIDTH - STAGE_HALF_WIDTH){1'b0}}, current_input_stage[STAGE_HALF_WIDTH-1:0]};
            end else begin
                assign pipeline_reg[i] = pipeline_reg[i-1] ^ {{(DATA_WIDTH - STAGE_HALF_WIDTH){1'b1}}, pipeline_reg[i-1][STAGE_HALF_WIDTH-1:0]};
            end
        end
    endgenerate
    assign data_out_p = pipeline_reg[NUM_STAGES-1];
endmodule
module ComplexDataStructures (
    input logic [7:0] data_a,
    input logic [7:0] data_b,
    input logic sel_union,
    input string key_in,
    input logic [31:0] val_in,
    output logic [15:0] union_out,
    output int array_sum
);
    typedef union packed {
        logic [15:0] int_val;
        struct packed {
            byte     byte0;
            byte     byte1;
        } byte_vals;
    } MyUnion_t;
    MyUnion_t my_union;
    int dynamic_array[];
    int associative_array[string];
    int my_queue[$];
    always_comb begin
        if (sel_union) begin
            my_union.byte_vals.byte0 = data_a;
            my_union.byte_vals.byte1 = data_b;
        end else begin
            my_union.int_val = {data_b, data_a};
        end
        union_out = my_union.int_val[15:0];
        dynamic_array = new[2];
        dynamic_array[0] = data_a;
        dynamic_array[1] = data_b;
        array_sum = dynamic_array[0] + dynamic_array[1];
        associative_array[key_in] = val_in;
        if (associative_array.exists("fixed_key")) begin
            array_sum = array_sum + associative_array["fixed_key"];
        end else begin
            associative_array["fixed_key"] = 50;
            array_sum = array_sum + 50;
        end
        my_queue.push_back(data_a);
        my_queue.push_front(data_b);
        if (my_queue.size() > 0) begin
            array_sum = array_sum + my_queue.pop_front();
        end
        my_queue.delete();
    end
endmodule
