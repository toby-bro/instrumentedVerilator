module CombinationalProcessor #(
    parameter int DATA_WIDTH = 16,
    parameter int SHIFT_AMT = 2
) (
    input logic [DATA_WIDTH-1:0] in_a,
    input logic [DATA_WIDTH-1:0] in_b,
    input byte                   select_op,
    output logic [DATA_WIDTH-1:0] out_result,
    output bit                   out_overflow
);
    localparam ADD_OP = 8'd0;
    localparam SUB_OP = 8'd1;
    localparam MUL_OP = 8'd2;
    localparam SHIFT_OP = 8'd3;
    logic [DATA_WIDTH:0] temp_sum;
    int                  intermediate_int;
    longint              large_value;
    assign large_value = in_a * 1000 + in_b;
    always_comb begin
        temp_sum = 0;
        out_result = 0;
        out_overflow = 0;
        intermediate_int = 0;
        case(select_op)
            ADD_OP: begin
                temp_sum = in_a + in_b;
                out_result = temp_sum[DATA_WIDTH-1:0];
                out_overflow = temp_sum[DATA_WIDTH];
            end
            SUB_OP: begin
                temp_sum = in_a - in_b;
                out_result = temp_sum[DATA_WIDTH-1:0];
            end
            MUL_OP: begin
                intermediate_int = in_a * in_b;
                out_result = intermediate_int[DATA_WIDTH-1:0];
                if (DATA_WIDTH <= 31) begin
                    out_overflow = (in_a * in_b) > ((1 << DATA_WIDTH) - 1);
                end else begin
                    out_overflow = 0;
                end
            end
            SHIFT_OP: begin
                out_result = in_a << SHIFT_AMT;
            end
            default: begin
                out_result = '0;
            end
        endcase
    end
endmodule
module SequentialRegisterBank #(
    parameter int BANK_DEPTH = 8,
    parameter int DATA_BITS = 32
) (
    input logic                    clk,
    input logic                    reset_n,
    input logic [DATA_BITS-1:0]    data_in,
    input logic [$clog2(BANK_DEPTH)-1:0] addr,
    input logic                    wr_en,
    output logic [DATA_BITS-1:0]   data_out
);
    logic [DATA_BITS-1:0] memory_bank [BANK_DEPTH];
    logic [7:0][7:0] config_reg;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            for (int i = 0; i < BANK_DEPTH; i++) begin
                memory_bank[i] <= '0;
            end
            config_reg <= '0;
        end else begin
            if (wr_en) begin
                memory_bank[addr] <= data_in;
                config_reg[0] <= data_in[7:0];
                config_reg[1] <= data_in[15:8];
            end
        end
    end
    assign data_out = memory_bank[addr];
endmodule
typedef struct packed {
    logic [3:0] id;
    logic [7:0] value;
    bit         valid;
} MyPacket_t;
typedef enum logic [1:0] {
    IDLE = 2'b00,
    PROCESSING = 2'b01,
    DONE = 2'b10,
    ERROR = 2'b11
} State_e;
typedef union {
    int   int_val;
    real  real_val;
    byte  byte_array[4];
} DataUnion_u;
class MyProcessorClass;
    localparam int CLASS_INTERNAL_PARAM = 10;
    rand int class_seed;
    MyPacket_t current_packet;
    State_e    current_state;
    DataUnion_u current_union_data;
    function new(int seed_val);
        class_seed = seed_val;
        current_packet.id = 0;
        current_packet.value = 0;
        current_packet.valid = 0;
        current_state = IDLE;
        current_union_data.int_val = 0;
    endfunction
    function void process_packet(MyPacket_t pkt);
        current_packet = pkt;
        current_state = PROCESSING;
        current_union_data.int_val = current_packet.value * CLASS_INTERNAL_PARAM;
        if (current_packet.valid) begin
            current_state = DONE;
        end else begin
            current_state = ERROR;
        end
    endfunction
    function MyPacket_t get_processed_packet();
        return current_packet;
    endfunction
    function State_e get_state();
        return current_state;
    endfunction
endclass
module CustomTypeHandler (
    input State_e     input_control,
    input MyPacket_t  data_value,
    output State_e    output_status,
    output MyPacket_t processed_data
);
    MyProcessorClass my_processor;
    State_e    internal_state;
    MyPacket_t internal_packet;
    DataUnion_u internal_union;
    always_comb begin
        if (my_processor == null) begin
            my_processor = new(123);
        end
        internal_state = input_control;
        internal_packet = data_value;
        my_processor.process_packet(internal_packet);
        output_status = my_processor.get_state();
        processed_data = my_processor.get_processed_packet();
        internal_union.int_val = 100;
    end
endmodule
module GenerateBlockExample #(
    parameter int NUM_STAGES = 4,
    parameter int DATA_WIDTH = 8,
    parameter bit ENABLE_REGISTER = 1
) (
    input logic                 clk,
    input logic                 reset_n,
    input logic [DATA_WIDTH-1:0] data_in,
    input logic                 enable,
    output logic [DATA_WIDTH-1:0] data_out
);
    logic [DATA_WIDTH-1:0] pipe_regs [NUM_STAGES];
    genvar j;
    for (j = 0; j < NUM_STAGES; j++) begin : pipeline_stage_gen
        if (ENABLE_REGISTER) begin : registered_stage
            always_ff @(posedge clk or negedge reset_n) begin
                if (!reset_n) begin
                    pipe_regs[j] <= '0;
                end else if (enable) begin
                    if (j == 0) begin
                        pipe_regs[j] <= data_in;
                    end else begin
                        pipe_regs[j] <= pipe_regs[j-1];
                    end
                end
            end
        end else begin : combinational_stage
            assign pipe_regs[j] = (j == 0) ? data_in : pipe_regs[j-1];
        end
    end
    assign data_out = pipe_regs[NUM_STAGES-1];
endmodule
module RealNumberProcessor (
    input real          input_real_a,
    input real          input_real_b,
    input byte          opcode,
    output real         output_real_result,
    output int          output_int_val
);
    localparam ADD_REAL = 8'h01;
    localparam SUB_REAL = 8'h02;
    localparam MULT_REAL = 8'h03;
    localparam DIV_REAL = 8'h04;
    localparam ROUND_TO_INT = 8'h05;
    function real calculate_real(real val_a, real val_b, byte op);
        real temp_result;
        case(op)
            ADD_REAL: temp_result = val_a + val_b;
            SUB_REAL: temp_result = val_a - val_b;
            MULT_REAL: temp_result = val_a * val_b;
            DIV_REAL: begin
                if (val_b != 0.0) temp_result = val_a / val_b;
                else temp_result = 0.0;
            end
            default: temp_result = 0.0;
        endcase
        return temp_result;
    endfunction
    task round_and_assign(real input_val, output int out_int);
        out_int = $rtoi(input_val);
    endtask 
    always_comb begin
        output_real_result = calculate_real(input_real_a, input_real_b, opcode);
        if (opcode == ROUND_TO_INT) begin
            round_and_assign(input_real_a, output_int_val);
        end else begin
            output_int_val = 0;
        end
    end
endmodule
