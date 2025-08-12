module BasicLogicSigned (
    input logic signed [7:0] in_a,
    input logic signed [7:0] in_b,
    input logic       sel_op,
    output logic signed [8:0] out_result,
    output logic       out_overflow
);
    logic signed [7:0] sum;
    logic signed [7:0] diff;
    always_comb begin
        sum = in_a + in_b;
        diff = in_a - in_b;
        if (sel_op) begin
            out_result = sum;
            out_overflow = ((in_a[7] == 1'b0) && (in_b[7] == 1'b0) && (sum[7] == 1'b1)) ||
                           ((in_a[7] == 1'b1) && (in_b[7] == 1'b1) && (sum[7] == 1'b0));
        end else begin
            out_result = diff;
            out_overflow = ((in_a[7] == 1'b0) && (in_b[7] == 1'b1) && (diff[7] == 1'b1)) ||
                           ((in_a[7] == 1'b1) && (in_b[7] == 1'b0) && (diff[7] == 1'b0));
        end
    end
endmodule
module StateMachine (
    input logic clk,
    input logic rst_n,
    input logic next_state_trigger,
    output logic [1:0] current_state_out,
    output logic state_active
);
    typedef enum logic [1:0] {
        IDLE = 2'b00,
        STATE1 = 2'b01,
        STATE2 = 2'b10,
        DONE = 2'b11
    } fsm_state_e;
    fsm_state_e current_state;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state = IDLE;
            state_active = 1'b0;
        end else begin
            state_active = 1'b1;
            case (current_state)
                IDLE: begin
                    if (next_state_trigger) begin
                        current_state = STATE1;
                    end
                end
                STATE1: begin
                    if (next_state_trigger) begin
                        current_state = STATE2;
                    end else begin
                        current_state = IDLE;
                    end
                end
                STATE2: begin
                    if (next_state_trigger) begin
                        current_state = DONE;
                    end else begin
                        current_state = STATE1;
                    end
                end
                DONE: begin
                    if (next_state_trigger) begin
                        current_state = IDLE;
                    end else begin
                        current_state = DONE;
                    end
                end
                default: current_state = IDLE;
            endcase
        end
    end
    assign current_state_out = current_state;
endmodule
module FuncTaskModule (
    input logic [3:0] in_val1,
    input logic [3:0] in_val2,
    input logic enable_task,
    output logic [4:0] out_sum,
    output logic [7:0] out_mul,
    output logic       task_status
);
    function automatic logic [4:0] add_values (logic [3:0] a, logic [3:0] b);
        return a + b;
    endfunction
    task automatic calculate_multiplication (input logic [3:0] val1, input logic [3:0] val2, output logic [7:0] result, output logic status);
        result = val1 * val2;
        status = (val1 > 0 && val2 > 0);
    endtask
    always_comb begin
        out_sum = add_values(in_val1, in_val2);
        task_status = 1'b0;
        out_mul = 8'b0;
        if (enable_task) begin
            calculate_multiplication(in_val1, in_val2, out_mul, task_status);
        end
    end
endmodule
module ArrayProcessor (
    input logic [7:0] in_data [3:0],
    input logic       reset_arr,
    output logic [7:0] out_max_val,
    output logic [1:0] out_max_idx
);
    logic [7:0] internal_array [3:0];
    logic [7:0] temp_max_val;
    logic [1:0] temp_max_idx;
    always_comb begin
        if (reset_arr) begin
            for (int i = 0; i < 4; i++) begin
                internal_array[i] = 8'h00;
            end
        end else begin
            for (int i = 0; i < 4; i++) begin
                internal_array[i] = in_data[i];
            end
        end
        temp_max_val = 8'h00;
        temp_max_idx = 2'b00;
        for (int i = 0; i < 4; i++) begin
            if (internal_array[i] > temp_max_val) begin
                temp_max_val = internal_array[i];
                temp_max_idx = i;
            end
        end
        out_max_val = temp_max_val;
        out_max_idx = temp_max_idx;
    end
endmodule
module StructUnionTypes (
    input logic [15:0] in_packed_val,
    input logic [7:0]  in_byte1,
    input logic [7:0]  in_byte2,
    input logic        select_union_field,
    output logic [15:0] out_struct_val,
    output logic [15:0] out_union_val
);
    typedef struct packed {
        logic [7:0] msb;
        logic [7:0] lsb;
    } my_packed_struct_t;
    typedef union {
        logic [15:0] word;
        logic [7:0] byte_array[2];
    } my_unpacked_union_t;
    my_packed_struct_t s_var;
    my_unpacked_union_t u_var;
    always_comb begin
        s_var.msb = in_byte1;
        s_var.lsb = in_byte2;
        out_struct_val = s_var;
        if (select_union_field) begin
            u_var.word = in_packed_val;
        end else begin
            u_var.byte_array[0] = in_byte1;
            u_var.byte_array[1] = in_byte2;
        end
        out_union_val = u_var.word;
    end
endmodule
module ClassUser (
    input logic clk,
    input logic rst_n,
    input logic enable_process,
    input logic [7:0] data_in,
    output logic [7:0] data_out,
    output logic       processed_flag
);
    class DataProcessor;
        rand logic [7:0] internal_data;
        logic [7:0] processed_data;
        function new();
            internal_data = 8'hAA;
            processed_data = 8'h00;
        endfunction
        function void process(logic [7:0] input_data);
            processed_data = ~input_data;
            internal_data = input_data;
        endfunction
        function logic [7:0] get_processed_data();
            return processed_data;
        endfunction
    endclass
    DataProcessor my_processor;
    logic [7:0] temp_data_out;
    logic temp_flag;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            my_processor = new();
            temp_data_out = 8'h00;
            temp_flag = 1'b0;
        end else begin
            if (enable_process) begin
                if (my_processor == null) begin
                    my_processor = new();
                end
                my_processor.process(data_in);
                temp_data_out = my_processor.get_processed_data();
                temp_flag = 1'b1;
            end else begin
                temp_flag = 1'b0;
            end
        end
    end
    assign data_out = temp_data_out;
    assign processed_flag = temp_flag;
endmodule
module ConfigurableRegisterBank #(
    parameter DATA_WIDTH = 8,
    parameter NUM_REGISTERS = 4
) (
    input logic clk,
    input logic rst_n,
    input logic [DATA_WIDTH-1:0] in_data,
    input logic [NUM_REGISTERS-1:0] write_enable_vec,
    output logic [DATA_WIDTH-1:0] out_reg_data [NUM_REGISTERS-1:0]
);
    logic [DATA_WIDTH-1:0] registers [NUM_REGISTERS-1:0];
    genvar i;
    generate
        for (i = 0; i < NUM_REGISTERS; i++) begin : gen_registers
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    registers[i] <= {DATA_WIDTH{1'b0}};
                end else if (write_enable_vec[i]) begin
                    registers[i] <= in_data;
                end
            end
        end
    endgenerate
    generate
        if (NUM_REGISTERS > 2) begin : large_bank_feature
            logic [DATA_WIDTH-1:0] sum_of_first_two;
            always_comb begin
                sum_of_first_two = registers[0] + registers[1];
            end
        end
    endgenerate
    always_comb begin
        for (int i = 0; i < NUM_REGISTERS; i++) begin
            out_reg_data[i] = registers[i];
        end
    end
endmodule
package MyTypesPackage;
    parameter CONST_MAX_COUNT = 10;
    typedef logic [7:0] byte_t;
    typedef enum {
        RED, GREEN, BLUE, YELLOW
    } color_e;
    function automatic byte_t clamp_value(byte_t val);
        return (val > CONST_MAX_COUNT) ? CONST_MAX_COUNT : val;
    endfunction
    function automatic logic [2:0] encode_color(color_e c);
        case (c)
            RED:    return 3'b001;
            GREEN:  return 3'b010;
            BLUE:   return 3'b100;
            YELLOW: return 3'b011;
            default: return 3'b000;
        endcase
    endfunction
endpackage
module PackageUser (
    input MyTypesPackage::byte_t in_val,
    input MyTypesPackage::color_e in_color,
    output MyTypesPackage::byte_t out_clamped_val,
    output logic [2:0] out_color_encoded
);
    import MyTypesPackage::*;
    always_comb begin
        out_clamped_val = clamp_value(in_val);
        out_color_encoded = encode_color(in_color);
    end
endmodule
module SimpleAssertion (
    input logic condition_in,
    input logic [3:0] data_in_assert,
    output logic assertion_pass,
    output logic [3:0] data_out_assert
);
    logic internal_check;
    always_comb begin
        data_out_assert = data_in_assert;
        internal_check = (data_in_assert > 4'd0);
        assert (!(condition_in && !internal_check));
        assertion_pass = !(condition_in && !internal_check);
    end
endmodule
module FixedSizeFIFO (
    input logic clk,
    input logic rst_n,
    input logic push_en,
    input logic pop_en,
    input logic [7:0] data_in_fifo,
    output logic [7:0] data_out_fifo,
    output logic       fifo_empty,
    output logic       fifo_full
);
    parameter FIFO_DEPTH = 4;
    logic [7:0] fifo_mem [FIFO_DEPTH-1:0];
    logic [$clog2(FIFO_DEPTH):0] head_ptr, tail_ptr;
    logic [FIFO_DEPTH:0] current_size;
    always_ff @(posedge clk or negedge rst_n) begin
        automatic logic do_push = push_en && !fifo_full;
        automatic logic do_pop = pop_en && !fifo_empty;
        if (!rst_n) begin
            head_ptr <= 0;
            tail_ptr <= 0;
            current_size <= 0;
        end else begin
            if (do_push && !do_pop) begin
                fifo_mem[tail_ptr] <= data_in_fifo;
                tail_ptr <= (tail_ptr + 1) % FIFO_DEPTH;
                current_size <= current_size + 1;
            end else if (!do_push && do_pop) begin
                head_ptr <= (head_ptr + 1) % FIFO_DEPTH;
                current_size <= current_size - 1;
            end else if (do_push && do_pop) begin
                fifo_mem[tail_ptr] <= data_in_fifo;
                tail_ptr <= (tail_ptr + 1) % FIFO_DEPTH;
                head_ptr <= (head_ptr + 1) % FIFO_DEPTH;
            end
        end
    end
    always_comb begin
        fifo_empty = (current_size == 0);
        fifo_full = (current_size == FIFO_DEPTH);
        data_out_fifo = (current_size == 0) ? 8'hFF : fifo_mem[head_ptr];
    end
endmodule
module AssociativeArrayDeclaration (
    input logic clk,
    input logic rst_n,
    input logic       write_en_aa,
    input logic [7:0] key_in_aa,
    input logic [15:0] val_in_aa,
    input logic       delete_en_aa,
    input logic [7:0] key_delete_aa,
    input logic       read_en_aa,
    input logic [7:0] key_read_aa,
    output logic [15:0] val_out_aa,
    output logic       found_aa,
    output logic [31:0] num_entries_out
);
    logic [15:0] my_assoc_array [logic [7:0]];
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            my_assoc_array.delete();
        end else begin
            if (write_en_aa) begin
                my_assoc_array[key_in_aa] = val_in_aa;
            end
            if (delete_en_aa) begin
                if (my_assoc_array.exists(key_delete_aa)) begin
                    my_assoc_array.delete(key_delete_aa);
                end
            end
        end
    end
    always_comb begin
        logic [15:0] read_val;
        if (read_en_aa && my_assoc_array.exists(key_read_aa)) begin
            read_val = my_assoc_array[key_read_aa];
            found_aa = 1'b1;
        end else begin
            read_val = 16'hFFFF;
            found_aa = 1'b0;
        end
        val_out_aa = read_val;
        num_entries_out = my_assoc_array.num();
    end
endmodule
