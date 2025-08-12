module CombinationalLogic (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic       sel,
    output logic [7:0] out_and,
    output logic [7:0] out_or,
    output logic [7:0] out_mux,
    output logic [7:0] out_case
);
    assign out_and = a & b;
    assign out_or  = a | b;
    always_comb begin
        if (sel) begin
            out_mux = a;
        end else begin
            out_mux = b;
        end
    end
    always_comb begin
        case (a[1:0]) 
            2'b00: out_case = b + 1;
            2'b01: out_case = b - 1;
            2'b10: out_case = b * 2;
            2'b11: out_case = b / 2; 
            default: out_case = b;   
        endcase
    end
endmodule
module SequentialState (
    input  logic       clk,
    input  logic       rst_n,
    input  logic [15:0] data_in,
    input  logic       load_en,
    output logic [15:0] data_out,
    output logic [2:0]  state_reg
);
    parameter START_COUNTER_VALUE = 16'hAAAA;
    parameter MAX_COUNT_VALUE     = 16'hFFFF;
    typedef enum logic [2:0] {
        IDLE,
        STATE_A,
        STATE_B,
        STATE_C,
        ERROR_STATE 
    } fsm_state_e;
    fsm_state_e current_state, next_state;
    typedef struct packed {
        logic [7:0] low_byte;
        logic [7:0] high_byte;
    } s_data_word;
    s_data_word internal_word; 
    logic [15:0] counter_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin 
            counter_reg   <= START_COUNTER_VALUE;
            current_state <= IDLE;
            internal_word.low_byte  <= 8'h00;
            internal_word.high_byte <= 8'h00;
        end else begin
            if (load_en) begin 
                counter_reg <= data_in;
                internal_word.low_byte  <= data_in[7:0];
                internal_word.high_byte <= data_in[15:8];
            end else begin
                if (counter_reg == MAX_COUNT_VALUE) begin
                    counter_reg <= START_COUNTER_VALUE; 
                end else begin
                    counter_reg <= counter_reg + 1;
                end
            end
            current_state <= next_state; 
        end
    end
    always_comb begin
        next_state = current_state; 
        case (current_state)
            IDLE:
                if (load_en) next_state = STATE_A;
            STATE_A:
                if (counter_reg[0]) next_state = STATE_B; 
                else next_state = IDLE;
            STATE_B:
                if (counter_reg[1]) next_state = STATE_C;
                else next_state = STATE_A;
            STATE_C:
                next_state = IDLE; 
            ERROR_STATE:
                next_state = IDLE; 
            default:
                next_state = ERROR_STATE; 
        endcase
    end
    assign data_out  = counter_reg;
    assign state_reg = current_state; 
endmodule
module FunctionalBlock (
    input  logic [7:0] arg1,
    input  logic [7:0] arg2,
    input  logic [1:0] op_code,      
    output logic [15:0] result_func,
    output logic [7:0] result_task
);
    function automatic [15:0] calculate_math_op(input logic [7:0] in1, input logic [7:0] in2, input logic is_sum);
        logic [15:0] temp_res;
        if (is_sum) begin
            temp_res = in1 + in2;
        end else begin
            temp_res = in1 - in2;
        end
        return temp_res;
    endfunction
    task automatic get_operation_result(input logic [1:0] op, input logic [7:0] val1, output logic [7:0] res);
        case (op)
            2'b00: res = val1 & 8'hAA; 
            2'b01: res = val1 | 8'h55; 
            2'b10: res = val1 ^ 8'hFF; 
            default: res = val1;       
        endcase
    endtask
    always_comb begin
        case (op_code)
            2'd0: result_func = calculate_math_op(arg1, arg2, 1'b1); 
            2'd1: result_func = calculate_math_op(arg1, arg2, 1'b0); 
            2'd2: result_func = arg1 * arg2; 
            default: result_func = 0;
        endcase
        get_operation_result(op_code, arg1, result_task);
    end
endmodule
module DataStructures (
    input  logic [2:0] idx,
    input  logic [7:0] val_in,
    input  logic       push_en,
    input  logic       pop_en,
    output logic [7:0] val_out_array,
    output logic [7:0] val_out_q
);
    logic [7:0] fixed_array [8]; 
    logic       fixed_array_initialized = 1'b0; 
    logic [7:0] dynamic_array [];
    localparam DYNAMIC_ARRAY_MAX_SIZE = 4; 
    logic [7:0] data_queue [$]; 
    always_comb begin
        if (!fixed_array_initialized) begin
            for (int i = 0; i < 8; i++) begin
                fixed_array[i] = i * 2; 
            end
            fixed_array_initialized = 1'b1;
        end
        if (idx < 8) begin
            val_out_array = fixed_array[idx];
        end else begin
            val_out_array = 8'hXX; 
        end
        if (push_en && dynamic_array.size() < DYNAMIC_ARRAY_MAX_SIZE) begin
            dynamic_array = new[dynamic_array.size() + 1](dynamic_array); 
            dynamic_array[dynamic_array.size() - 1] = val_in;
        end else if (pop_en && dynamic_array.size() > 0) begin
            dynamic_array = new[dynamic_array.size() - 1](dynamic_array);
        end
        val_out_q = 8'h00; 
        if (push_en) begin
            data_queue.push_back(val_in + 10); 
        end else if (pop_en && data_queue.size() > 0) begin
            val_out_q = data_queue.pop_front(); 
        end else if (data_queue.size() > 0) begin
            val_out_q = data_queue[0]; 
        end
    end
endmodule
class MyProcessor;
    rand int data_x; 
    int data_y;
    int result_internal;
    function new(int init_x, int init_y);
        data_x = init_x;
        data_y = init_y;
        result_internal = 0;
    endfunction
    function int add_operation();
        result_internal = data_x + data_y;
        return result_internal;
    endfunction
    function int subtract_operation();
        result_internal = data_x - data_y;
        return result_internal;
    endfunction
    function void update_data(int new_x, int new_y);
        data_x = new_x;
        data_y = new_y;
    endfunction
endclass
module ObjectOrientedSV (
    input  logic [7:0] val_a,
    input  logic [7:0] val_b,
    input  logic [1:0] op_mode,      
    output logic [31:0] object_result
);
    MyProcessor my_proc_handle;
    always_comb begin
        object_result = 0; 
        if (my_proc_handle == null || op_mode == 2'd3) begin 
            my_proc_handle = new(val_a, val_b); 
        end
        if (my_proc_handle != null) begin 
            case (op_mode)
                2'd0: object_result = my_proc_handle.add_operation();
                2'd1: object_result = my_proc_handle.subtract_operation();
                2'd2: begin
                    my_proc_handle.update_data(val_a + 1, val_b + 1); 
                    object_result = my_proc_handle.result_internal; 
                end
                default: begin
                    object_result = my_proc_handle.data_x + my_proc_handle.data_y; 
                end
            endcase
        end
    end
endmodule
