package my_pkg;
    class MySimpleClass;
        logic [7:0] internal_counter;
        function new(logic [7:0] initial_val);
            this.internal_counter = initial_val;
        endfunction
        function logic [7:0] process_value(logic [7:0] input_val);
            internal_counter = internal_counter + 1;
            return internal_counter + input_val;
        endfunction
        function void reset_counter();
            this.internal_counter = 8'b0;
        endfunction
    endclass
endpackage
module LogicAndArithmetic (
    input logic [7:0]   in_val_a,
    input bit           in_flag_b,
    input byte          in_byte_c,
    output logic [15:0] out_complex_sum,
    output int          out_signed_result,
    output bit          out_parity
);
    logic [7:0]  intermediate_calc;
    int          signed_temp;
    always_comb begin
        if (in_flag_b) begin
            intermediate_calc = in_val_a | in_byte_c;
            signed_temp = $signed(in_val_a) + 20;
        end else begin
            intermediate_calc = in_val_a & ~in_byte_c;
            signed_temp = $signed(in_byte_c) - 5;
        end
        out_signed_result = signed_temp;
    end
    assign out_complex_sum = ({8'b0, in_val_a} + {8'b0, in_byte_c}) << 1;
    always_comb begin
        out_parity = ^intermediate_calc;
    end
endmodule
module DataStructureProcessor (
    input bit [1:0]    in_mode_select,
    input logic [7:0]  in_data_x,
    input logic [7:0]  in_data_y,
    input logic [15:0] in_packed_word,
    output logic [15:0] out_processed_data,
    output bit         out_error_flag
);
    typedef enum logic [1:0] {
        MODE_IDLE,
        MODE_PROCESS_X,
        MODE_PROCESS_Y,
        MODE_ERROR
    } processing_mode_e;
    typedef struct packed {
        logic [7:0] upper_byte;
        logic [7:0] lower_byte;
    } s_bytes_t;
    typedef union packed {
        logic [15:0] full_val;
        s_bytes_t    split_val;
    } u_word_t;
    processing_mode_e current_mode;
    s_bytes_t         my_struct_var;
    u_word_t          my_union_var;
    always_comb begin
        my_struct_var.upper_byte = in_data_x;
        my_struct_var.lower_byte = in_data_y;
        my_union_var.full_val = in_packed_word;
        out_error_flag = 1'b0;
        case (in_mode_select)
            MODE_IDLE: begin
                current_mode = MODE_IDLE;
                out_processed_data = 16'h0000;
            end
            MODE_PROCESS_X: begin
                current_mode = MODE_PROCESS_X;
                out_processed_data = {my_struct_var.upper_byte, my_union_var.split_val.lower_byte};
            end
            MODE_PROCESS_Y: begin
                current_mode = MODE_PROCESS_Y;
                out_processed_data = {my_union_var.split_val.upper_byte, my_struct_var.lower_byte};
            end
            default: begin
                current_mode = MODE_ERROR;
                out_processed_data = 16'hFFFF;
                out_error_flag = 1'b1;
            end
        endcase
    end
endmodule
module ClassHandlerModule (
    input logic [7:0]   in_initial_val,
    input logic [7:0]   in_process_val,
    input bit           in_reset_command,
    output logic [7:0]  out_processed_result
);
    import my_pkg::*;
    MySimpleClass my_object_instance;
    always_comb begin
        my_object_instance = new(in_initial_val);
        if (in_reset_command) begin
            my_object_instance.reset_counter();
        end
        out_processed_result = my_object_instance.process_value(in_process_val);
    end
endmodule
module ParameterizedArrayOps #(
    parameter int ARRAY_SIZE = 8,
    parameter int DATA_WIDTH = 4
) (
    input logic [DATA_WIDTH-1:0] in_data_array [ARRAY_SIZE-1:0],
    input bit                    in_calculate,
    output logic [DATA_WIDTH:0]  out_array_sum,
    output logic [DATA_WIDTH-1:0] out_max_value
);
    logic [DATA_WIDTH:0]  local_sum;
    logic [DATA_WIDTH-1:0] local_max;
    integer i;
    always_comb begin
        local_sum = '0;
        local_max = '0;
        if (in_calculate) begin
            for (i = 0; i < ARRAY_SIZE; i = i + 1) begin
                local_sum = local_sum + in_data_array[i];
                if (in_data_array[i] > local_max) begin
                    local_max = in_data_array[i];
                end
            end
        end else begin
            local_sum = 'X;
            local_max = 'X;
        end
        out_array_sum = local_sum;
        out_max_value = local_max;
    end
endmodule
module AdvancedTypesAndOperators (
    input  real           in_float_a,
    input  shortreal      in_sfloat_b,
    input  int signed     in_sint_c,
    input  bit [7:0]      in_unsigned_d,
    output real           out_float_product,
    output int signed     out_sint_shifted,
    output logic [15:0]   out_concat_replicate
);
    real          temp_real_mul;
    int signed    temp_signed_op;
    logic [15:0]  temp_concat;
    always_comb begin
        temp_real_mul = in_float_a * in_sfloat_b;
        out_float_product = temp_real_mul / 3.0;
        temp_signed_op = in_sint_c + $signed({8'b0, in_unsigned_d});
        out_sint_shifted = temp_signed_op >>> 1;
        temp_concat = ({2{in_unsigned_d}}) << 2;
        out_concat_replicate = temp_concat;
    end
endmodule
