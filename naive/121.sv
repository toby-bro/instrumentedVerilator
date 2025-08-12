module BasicCombinationalLogic (
    input logic [7:0] in_data_a,
    input logic [7:0] in_data_b,
    input logic       in_control,
    output logic [8:0] out_result_sum,
    output logic       out_greater
);
    parameter DATA_WIDTH = 8;
    localparam MAX_VALUE = (1 << DATA_WIDTH) - 1;
    typedef enum logic [1:0] {
        STATE_IDLE,
        STATE_ADD,
        STATE_SUBTRACT
    } OperationState_e;
    typedef struct packed {
        logic [DATA_WIDTH-1:0] field1;
        logic [DATA_WIDTH-1:0] field2;
    } DataPair_t;
    DataPair_t data_pair_local;
    OperationState_e current_op_state;
    always_comb begin
        data_pair_local.field1 = in_data_a;
        data_pair_local.field2 = in_data_b;
        if (in_control) begin
            out_result_sum = data_pair_local.field1 + data_pair_local.field2;
            current_op_state = STATE_ADD;
        end else begin
            out_result_sum = data_pair_local.field1 - data_pair_local.field2;
            current_op_state = STATE_SUBTRACT;
        end
        out_greater = (in_data_a > in_data_b);
    end
endmodule
module SequentialFSM (
    input logic        clk,
    input logic        rst_n,
    input logic [1:0]  input_code,
    output logic [3:0] current_state_out,
    output logic       operation_done
);
    typedef enum logic [3:0] {
        IDLE_S,
        INIT_S,
        PROCESS_A_S,
        PROCESS_B_S,
        FINISH_S
    } State_t;
    State_t current_state, next_state;
    reg [7:0] counter;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state <= IDLE_S;
            counter <= 8'd0;
            operation_done <= 1'b0;
        end else begin
            current_state <= next_state;
            if (current_state == PROCESS_A_S) begin
                counter <= counter + 8'd1;
            end else if (current_state == PROCESS_B_S) begin
                counter <= counter - 8'd1;
            end
            operation_done <= (next_state == FINISH_S);
        end
    end
    always_comb begin
        next_state = current_state;
        current_state_out = current_state;
        case (current_state)
            IDLE_S: begin
                if (input_code == 2'b01)
                    next_state = INIT_S;
            end
            INIT_S: begin
                if (counter == 8'd0)
                    next_state = PROCESS_A_S;
                else
                    next_state = IDLE_S;
            end
            PROCESS_A_S: begin
                if (counter >= 8'd5)
                    next_state = PROCESS_B_S;
            end
            PROCESS_B_S: begin
                if (counter <= 8'd2)
                    next_state = FINISH_S;
            end
            FINISH_S: begin
                next_state = IDLE_S;
            end
            default: begin
                next_state = IDLE_S;
            end
        endcase
    end
endmodule
class DataProcessor;
    rand int data_in;
    int data_out;
    function new(int initial_val);
        this.data_in = initial_val;
    endfunction
    function int process_data(int multiplier);
        data_out = data_in * multiplier;
        return data_out;
    endfunction
endclass
module ClassAndTaskFunctionUsage (
    input logic [15:0]  input_val_a,
    input logic [7:0]   input_multiplier,
    output logic [31:0] processed_result_a,
    output logic [15:0] processed_result_b
);
    function automatic int my_adder_func(int a, int b);
        return a + b;
    endfunction
    task automatic my_processor_task(input int val_in, output int val_out);
        val_out = val_in * 2 + my_adder_func(val_in, 10);
    endtask
    DataProcessor dp_handle;
    int temp_processed_val;
    always_comb begin
        dp_handle = new(input_val_a);
        processed_result_a = dp_handle.process_data(input_multiplier);
        my_processor_task(input_val_a[15:0], temp_processed_val);
        processed_result_b = my_adder_func(temp_processed_val, input_val_a[7:0]);
    end
endmodule
module ArrayAndLoopExamples (
    input logic [3:0]   select_idx,
    input logic [7:0]   data_in_array_val,
    output logic [7:0]  output_sum,
    output logic [7:0]  output_selected_val
);
    localparam NUM_ELEMENTS = 4;
    typedef logic [7:0] DataArray_t [NUM_ELEMENTS];
    typedef logic [NUM_ELEMENTS*8-1:0] PackedDataArray_t;
    DataArray_t my_unpacked_array;
    PackedDataArray_t my_packed_array;
    always_comb begin
        output_sum = 8'h0;
        output_selected_val = 8'h0;
        for (int i = 0; i < NUM_ELEMENTS; i++) begin
            my_unpacked_array[i] = data_in_array_val + i;
            output_sum = output_sum + my_unpacked_array[i];
        end
        for (int i = 0; i < NUM_ELEMENTS; i++) begin
            my_packed_array[i*8 +: 8] = data_in_array_val + i + 10;
        end
        if (select_idx < NUM_ELEMENTS) begin
            output_selected_val = my_packed_array[select_idx*8 +: 8];
        end else begin
            output_selected_val = 8'hFF;
        end
    end
endmodule
module UnionAndConditionalLogic (
    input logic [15:0]  input_a,
    input logic [15:0]  input_b,
    input logic [1:0]   mode_select,
    output logic [15:0] union_output,
    output logic [15:0] conditional_output
);
    typedef union packed {
        logic [15:0] word_data;
        struct packed {
            logic [7:0] lower_byte;
            logic [7:0] upper_byte;
        } byte_access;
    } DataUnion_t;
    DataUnion_t my_union;
    always_comb begin
        my_union.word_data = input_a;
        union_output = my_union.byte_access.lower_byte + my_union.byte_access.upper_byte;
        conditional_output = (input_a > input_b) ? input_a : input_b;
        unique case (mode_select)
            2'b00: conditional_output = conditional_output + input_a;
            2'b01: conditional_output = conditional_output - input_b;
            2'b10: conditional_output = conditional_output << 1;
            2'b11: conditional_output = conditional_output >> 1;
        endcase
    end
    generate
        if (1) begin : gen_block_always_active
            localparam OPERATION_ENABLED = 1;
        end else begin : gen_block_never_active
            localparam OPERATION_ENABLED = 0;
        end
    endgenerate
endmodule
