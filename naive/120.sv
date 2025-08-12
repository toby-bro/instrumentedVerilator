module SimpleCombinational (
    input logic [7:0] data_in,
    input logic       enable_i,
    output logic [7:0] result_out
);
    parameter DATA_WIDTH = 8;
    localparam MAX_VAL = 255; 
    logic [DATA_WIDTH-1:0] intermediate_val;
    always_comb begin
        if (enable_i) begin
            intermediate_val = data_in + 1; 
            if (intermediate_val > MAX_VAL) begin 
                result_out = {1'b0, data_in[6:0]}; 
            end else begin
                result_out = intermediate_val & 8'hF0; 
            end
        end else begin
            result_out = ~data_in; 
        end
    end
endmodule
module RegisterBlock (
    input logic clk_i,
    input logic rst_n_i, 
    input logic [3:0] d_in,
    output logic [3:0] q_out
);
    logic [3:0] internal_reg;
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin 
            internal_reg <= 4'b0; 
        end else begin
            internal_reg <= d_in;
        end
    end
    assign q_out = internal_reg; 
endmodule
module TaskFunctionDemo (
    input logic [15:0] operand_a,
    input logic [15:0] operand_b,
    input logic        perform_sub_i,
    output logic [15:0] calc_result_o
);
    function automatic logic [15:0] my_adder(input logic [15:0] val1, input logic [15:0] val2);
        logic [15:0] temp_sum; 
        temp_sum = val1 + val2; 
        return temp_sum;
    endfunction
    task automatic my_subtracter(input logic [15:0] val1, input logic [15:0] val2, output logic [15:0] diff_out);
        diff_out = val1 - val2; 
    endtask
    logic [15:0] internal_result;
    always_comb begin
        if (perform_sub_i) begin
            my_subtracter(operand_a, operand_b, internal_result); 
        end else begin
            internal_result = my_adder(operand_a, operand_b); 
        end
    end
    assign calc_result_o = internal_result;
endmodule
module TypeDefExamples (
    input logic [1:0] operation_select_i,
    input logic [7:0] data_value_i,
    output logic [7:0] processed_data_o
);
    typedef enum logic [1:0] {
        OP_ADD = 2'b00,
        OP_SUB = 2'b01,
        OP_MUL = 2'b10,
        OP_DIV = 2'b11
    } OperationType_e;
    typedef struct packed {
        OperationType_e op_type;
        logic [7:0]     operand;
    } Instruction_t;
    Instruction_t current_instruction;
    logic [7:0]   local_result;
    always_comb begin
        current_instruction.op_type = OperationType_e'(operation_select_i); 
        current_instruction.operand = data_value_i;
        case (current_instruction.op_type) 
            OP_ADD: local_result = current_instruction.operand + 8'd10;
            OP_SUB: local_result = current_instruction.operand - 8'd5;
            OP_MUL: local_result = current_instruction.operand * 8'd2;
            OP_DIV: begin
                if (current_instruction.operand != 0)
                    local_result = current_instruction.operand / 8'd2;
                else
                    local_result = 8'hFF; 
            end
            default: local_result = 8'b0; 
        endcase
    end
    assign processed_data_o = local_result;
endmodule
module ClassUsageExample (
    input logic enable_class_op_i,
    input logic [7:0] data_for_class_i,
    output logic [7:0] class_op_result_o
);
    class MyDataProcessor;
        rand int m_internal_val; 
        function new(); 
            m_internal_val = 0;
        endfunction
        function void set_value(int val); 
            m_internal_val = val;
        endfunction
        function int get_double_value(); 
            return m_internal_val * 2;
        endfunction
    endclass : MyDataProcessor
    MyDataProcessor local_processor_handle; 
    logic [7:0] temp_class_result;
    always_comb begin
        local_processor_handle = new(); 
        if (enable_class_op_i) begin
            local_processor_handle.set_value(data_for_class_i); 
            temp_class_result = local_processor_handle.get_double_value(); 
        end else begin
            temp_class_result = 8'b0;
        end
    end
    assign class_op_result_o = temp_class_result;
endmodule
module GenerateExampleRevised (
    input logic [1:0] sel_idx_i,
    input logic [7:0] data_inputs_i [4], 
    output logic [7:0] result_sel_o
);
    logic [7:0] processed_data [4]; 
    generate
        for (genvar i = 0; i < 4; i++) begin : LogicBlock
            if (i % 2 == 0) begin 
                assign processed_data[i] = ~data_inputs_i[i]; 
            end else begin 
                assign processed_data[i] = data_inputs_i[i];
            end
        end
    endgenerate
    always_comb begin
        result_sel_o = processed_data[sel_idx_i]; 
    end
endmodule
module ArrayManipulation (
    input logic [3:0][7:0] packed_matrix_in, 
    input logic [7:0] unpacked_array_in [2], 
    output logic [15:0] concatenated_out,
    output logic [7:0] sum_rows_o [2] 
);
    logic [7:0] temp_row_sum;
    logic [7:0] unpacked_sum;
    always_comb begin
        concatenated_out = {packed_matrix_in[0], packed_matrix_in[3]};
        unpacked_sum = unpacked_array_in[0] + unpacked_array_in[1];
        sum_rows_o[0] = unpacked_sum;
        temp_row_sum = packed_matrix_in[1][7:4] + packed_matrix_in[2][3:0]; 
        sum_rows_o[1] = temp_row_sum;
    end
endmodule
module RealArithmetic (
    input real          input_real_val_i,
    input int           input_int_val_i,
    input logic         enable_multiply_i,
    output real         output_real_res_o
);
    real temp_real_result;
    int  temp_int_result;
    always_comb begin
        if (enable_multiply_i) begin
            temp_real_result = input_real_val_i * $itor(input_int_val_i); 
        end else begin
            temp_real_result = input_real_val_i / 2.0; 
        end
        temp_int_result = $rtoi(temp_real_result); 
        output_real_res_o = temp_real_result + 1.5;
    end
endmodule
module LocalParamReduction (
    input logic [63:0] big_data_i,
    input logic        control_bit_i,
    output logic       any_one_o,
    output logic [7:0] byte_sum_o
);
    localparam MSB_BIT = 63;
    localparam LSB_BIT = 0;
    localparam HALF_WIDTH = 32;
    logic [MSB_BIT:LSB_BIT] shifted_data;
    logic [7:0] byte_accumulator;
    always_comb begin
        if (control_bit_i) begin
            shifted_data = big_data_i >> HALF_WIDTH; 
        end else begin
            shifted_data = big_data_i << HALF_WIDTH; 
        end
        any_one_o = |shifted_data; 
        byte_accumulator = 8'b0;
        for (int i = 0; i < 8; i++) begin 
            byte_accumulator = byte_accumulator + shifted_data[i*8 +: 8]; 
        end
        byte_sum_o = byte_accumulator;
    end
endmodule
module PackedUnionExample (
    input logic [15:0] union_data_in,
    input logic        select_high_byte_i,
    output logic [7:0] extracted_byte_o
);
    typedef union packed {
        logic [15:0] word;
        struct packed {
            logic [7:0] low_byte;
            logic [7:0] high_byte;
        } bytes;
    } WordOrBytes_u;
    WordOrBytes_u my_union;
    logic [7:0]   temp_extracted;
    always_comb begin
        my_union.word = union_data_in; 
        if (select_high_byte_i) begin
            temp_extracted = my_union.bytes.high_byte; 
        end else begin
            temp_extracted = my_union.bytes.low_byte; 
        end
    end
    assign extracted_byte_o = temp_extracted;
endmodule
module DoWhileLoopExample (
    input logic [7:0] start_val_i,
    input logic [7:0] limit_val_i,
    output logic [7:0] sum_upto_limit_o
);
    function automatic logic [7:0] calculate_sum(input logic [7:0] start, input logic [7:0] limit);
        logic [7:0] current_sum = 0;
        logic [7:0] counter = start;
        if (start <= limit) begin
            do begin 
                current_sum = current_sum + counter;
                counter++;
            end while (counter <= limit);
        end
        return current_sum;
    endfunction
    logic [7:0] internal_sum;
    always_comb begin
        internal_sum = calculate_sum(start_val_i, limit_val_i); 
    end
    assign sum_upto_limit_o = internal_sum;
endmodule
module PortVariety (
    input logic [15:0] wide_in_i,
    input logic [3:0] narrow_in_i,
    output logic [15:0] wide_out_o,
    output logic [3:0] narrow_out_o
);
    always_comb begin
        wide_out_o = wide_in_i + 1;
        narrow_out_o = narrow_in_i ^ 4'b1111; 
    end
endmodule
