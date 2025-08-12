module CombinationalProcessor (
    input logic clk,
    input logic reset_n,
    input logic [7:0] data_in,
    input logic [1:0] op_code,
    output logic [7:0] data_out,
    output logic [2:0] status_reg
);
    parameter IDLE_STATUS  = 3'b000;
    parameter PROC_STATUS  = 3'b001;
    parameter ERROR_STATUS = 3'b010;
    typedef enum logic [1:0] {
        OP_PASS = 2'b00,
        OP_INVERT = 2'b01,
        OP_ADD_ONE = 2'b10,
        OP_SUB_ONE = 2'b11
    } operation_t;
    logic [7:0] current_data_reg;
    logic [2:0] internal_status;
    logic [7:0] comb_result;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            current_data_reg <= 8'h00;
            internal_status  <= IDLE_STATUS;
        end else begin
            current_data_reg <= comb_result;
            internal_status  <= PROC_STATUS;
            if (op_code == 2'b11 && data_in == 8'h00) begin
                internal_status <= ERROR_STATUS;
            end
        end
    end
    always_comb begin
        case (operation_t'(op_code))
            OP_PASS:    comb_result = data_in;
            OP_INVERT:  comb_result = ~data_in;
            OP_ADD_ONE: comb_result = data_in + 8'h01;
            OP_SUB_ONE: comb_result = data_in - 8'h01;
            default:    comb_result = 8'hXX;
        endcase
    end
    assign data_out = current_data_reg;
    assign status_reg = internal_status;
endmodule
module MemoryBlock (
    input logic clk,
    input logic write_en,
    input logic [3:0] addr,
    input logic [15:0] data_write,
    output logic [15:0] data_read
);
    logic [15:0] memory [0:15];
    always_ff @(posedge clk) begin
        if (write_en) begin
            memory[addr] <= data_write;
        end
    end
    assign data_read = memory[addr];
endmodule
class SimpleRegister;
    rand logic [7:0] data_value;
    function new(logic [7:0] initial_val);
        data_value = initial_val;
    endfunction
    function void set_data(logic [7:0] val);
        this.data_value = val;
    endfunction
    function logic [7:0] get_data();
        return this.data_value;
    endfunction
endclass
module RegisterBankWithClass (
    input logic clk,
    input logic reset,
    input logic [7:0] set_value,
    input logic enable_set,
    output logic [7:0] current_value,
    output logic was_set_latch
);
    SimpleRegister reg_instance;
    logic [7:0] internal_data;
    logic internal_was_set;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            reg_instance = new(8'h00);
            internal_data = 8'h00;
            internal_was_set = 1'b0;
        end else begin
            if (enable_set) begin
                if (reg_instance == null) begin
                    reg_instance = new(set_value);
                end else begin
                    reg_instance.set_data(set_value);
                end
                internal_data = set_value;
                internal_was_set = 1'b1;
            end else begin
                if (reg_instance != null) begin
                    internal_data = reg_instance.get_data();
                end else begin
                    internal_data = 8'h00;
                end
                internal_was_set = 1'b0;
            end
        end
    end
    assign current_value = internal_data;
    assign was_set_latch = internal_was_set;
endmodule
module DataProcessor (
    input logic clk,
    input logic process_en,
    input logic [23:0] input_raw_data,
    output logic [15:0] processed_output_data,
    output logic [2:0] status_flags
);
    typedef struct packed {
        logic [7:0] identifier;
        logic [15:0] payload_value;
    } s_packet_t;
    typedef union packed {
        s_packet_t as_packet;
        logic [23:0] as_raw_word;
    } u_data_t;
    s_packet_t  internal_packet_reg;
    u_data_t    current_input_union;
    logic [2:0] internal_status;
    logic [2:0] next_status_val;
    logic [15:0] comb_output_data;
    assign current_input_union.as_raw_word = input_raw_data;
    always_comb begin
        if (internal_packet_reg.identifier != 8'h00) begin
            comb_output_data = internal_packet_reg.payload_value + internal_packet_reg.identifier;
            if (internal_packet_reg.identifier > 8'd100) begin
                next_status_val = 3'b001;
            end else begin
                next_status_val = 3'b010;
            end
        end else begin
            comb_output_data = 16'hFFFF;
            next_status_val = 3'b011;
        end
    end
    always_ff @(posedge clk) begin
        if (process_en) begin
            internal_packet_reg <= current_input_union.as_packet;
            internal_status <= next_status_val;
        end else begin
            internal_packet_reg <= '0;
            internal_status <= 3'b111;
        end
    end
    assign processed_output_data = comb_output_data;
    assign status_flags = internal_status;
endmodule
module FunctionTaskExecutor (
    input logic clk,
    input logic execute_op_en,
    input logic [7:0] operand_a,
    input logic [7:0] operand_b,
    input logic [1:0] operation_code,
    output logic [15:0] result,
    output logic error_out
);
    logic [15:0] internal_result;
    logic        internal_error;
    function automatic logic [15:0] compute_result (
        input logic [7:0] val1,
        input logic [7:0] val2,
        input logic [1:0] op_code_f
    );
        automatic logic [15:0] func_res;
        case (op_code_f)
            2'b00: func_res = val1 + val2;
            2'b01: func_res = val1 - val2;
            2'b10: func_res = val1 * val2;
            default: func_res = 16'hDEAD;
        endcase
        return func_res;
    endfunction
    task automatic execute_and_report (
        input logic [7:0] in_a,
        input logic [7:0] in_b,
        input logic [1:0] op_code_t,
        output logic [15:0] out_res,
        output logic out_err
    );
        out_err = 1'b0;
        case (op_code_t)
            2'b00: out_res = in_a + in_b;
            2'b01: out_res = in_a - in_b;
            2'b10: out_res = in_a * in_b;
            default: begin
                out_res = 16'hFFFF;
                out_err = 1'b1;
            end
        endcase
    endtask
    always_ff @(posedge clk) begin
        if (execute_op_en) begin
            execute_and_report(operand_a, operand_b, operation_code, internal_result, internal_error);
        end else begin
            internal_result <= compute_result(operand_a, operand_b, 2'b10);
            internal_error  <= 1'b0;
        end
    end
    assign result = internal_result;
    assign error_out = internal_error;
endmodule
module ComplexArrayManipulator (
    input logic clk,
    input logic reset,
    input logic [1:0] array_index,
    input logic [7:0] input_value,
    input logic write_enable,
    output logic [7:0] read_value,
    output logic [15:0] array_sum
);
    logic [7:0] data_array [4];
    logic [15:0] internal_sum;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            for (int i=0; i<4; i++) begin
                data_array[i] <= 8'h00;
            end
        end else if (write_enable) begin
            data_array[array_index] <= input_value;
        end
    end
    assign read_value = data_array[array_index];
    always_comb begin
        internal_sum = 16'b0;
        for (int i=0; i<4; i++) begin
            internal_sum = internal_sum + data_array[i];
        end
    end
    assign array_sum = internal_sum;
endmodule
