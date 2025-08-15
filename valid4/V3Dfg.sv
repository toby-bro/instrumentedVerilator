module ArithmeticLogic (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic [3:0] in_c,
    input logic       in_en,
    output logic [7:0] out_sum,
    output logic [7:0] out_diff,
    output logic       out_and,
    inout logic [7:0] io_data
);
    logic [7:0] prod_intermediate;
    logic [7:0] div_res_intermediate;
    logic [7:0] mod_res_intermediate;
    logic       neg_en_val;
    logic       or_res_val;
    logic [7:0] combined_io_data_calc;
    assign out_sum = in_a + in_b;
    assign out_diff = in_a - in_b;
    assign prod_intermediate = in_a * in_c;
    assign div_res_intermediate = in_a / 2'd2;
    assign mod_res_intermediate = in_b % 3'b111;
    assign neg_en_val = !in_en;
    assign or_res_val = in_en || neg_en_val;
    assign out_and = (in_a > in_b) && in_en;
    assign combined_io_data_calc = (or_res_val) ? (prod_intermediate + mod_res_intermediate) : div_res_intermediate;
    assign io_data = combined_io_data_calc;
    logic [7:0] dead_var_1;
    logic [7:0] dead_var_2;
    logic [7:0] dead_var_3;
    logic [7:0] dead_var_4;
    logic [7:0] dead_var_5;
    assign dead_var_1 = in_a + 8'd0;
    assign dead_var_2 = in_b * 8'd1;
    assign dead_var_3 = (in_a & in_b) & (in_a & in_b);
    assign dead_var_4 = in_c | in_c;
    assign dead_var_5 = dead_var_1 + dead_var_2;
endmodule
module BitManipulation (
    input logic [15:0] data_in,
    input logic [3:0] sel_idx,
    input logic [2:0] replicate_val_in,
    output logic [7:0] selected_bits_out,
    output logic [31:0] concatenated_out,
    output logic [23:0] replicated_output_val
);
    logic [7:0] upper_byte_val;
    logic [7:0] lower_byte_val;
    logic [7:0] bitwise_and_res;
    logic [7:0] bitwise_xor_res;
    logic [15:0] shifted_data_left;
    logic signed [15:0] signed_data_in_local;
    logic signed [15:0] signed_shifted_right_res;
    logic [23:0] temp_replicated_output_val;
    assign upper_byte_val = data_in[15:8];
    assign lower_byte_val = data_in[7:0];
    assign selected_bits_out = data_in[sel_idx +: 8];
    assign bitwise_and_res = upper_byte_val & lower_byte_val;
    assign bitwise_xor_res = upper_byte_val ^ lower_byte_val;
    assign shifted_data_left = data_in << 2;
    assign signed_data_in_local = signed'(data_in);
    assign signed_shifted_right_res = signed_data_in_local >>> 3;
    assign concatenated_out = {upper_byte_val, lower_byte_val, 8'hAA, 8'h55};
    assign temp_replicated_output_val = {3{replicate_val_in}};
    assign replicated_output_val = {temp_replicated_output_val[23:8],
                                    temp_replicated_output_val[7:0] + signed_shifted_right_res[7:0]};
endmodule
module ConditionalLogic (
    input logic [1:0] sel_in,
    input logic [7:0] val_a,
    input logic [7:0] val_b,
    input logic [7:0] val_c,
    output logic [7:0] result_if,
    output logic [7:0] result_case,
    output logic [7:0] result_ternary
);
    logic [7:0] temp_result_if;
    logic [7:0] deeply_nested_val;
    logic [7:0] intermediate_ternary_val;
    always_comb begin
        if (sel_in == 2'b00) begin
            temp_result_if = val_a + val_b;
        end else if (sel_in == 2'b01) begin
            temp_result_if = val_a - val_b;
        end else begin
            temp_result_if = val_c;
        end
    end
    always_comb begin
        case (sel_in)
            2'b00: result_case = val_a & val_c;
            2'b01: result_case = val_b | val_c;
            default: result_case = val_a ^ val_b;
        endcase
    end
    assign intermediate_ternary_val = (sel_in == 2'b10) ? (val_a + val_c) :
                                      ((sel_in == 2'b11) ? (val_b - val_c) : (val_a + val_b + val_c));
    assign result_ternary = intermediate_ternary_val;
    assign deeply_nested_val = (val_a > val_b) ?
                               ((val_c == 8'd0) ? (val_a * 2) : (val_b / 2)) :
                               ((val_a < val_c) ? (val_b + 1) : (val_c - 1));
    assign result_if = temp_result_if + deeply_nested_val;
endmodule
module UnpackedArrayModule (
    input logic [7:0] in_data,
    input logic [1:0] addr,
    output logic [7:0] array_read_out,
    output logic [7:0] array_write_verify
);
    logic [7:0] my_unpacked_array [0:3];
    logic [7:0] another_array [0:3];
    logic [7:0] copied_array[0:3];
    logic [7:0] temp_another_array_read;
    always_comb begin
        my_unpacked_array[0] = in_data + 8'd1;
        my_unpacked_array[1] = in_data + 8'd2;
        my_unpacked_array[2] = in_data + 8'd3;
        my_unpacked_array[3] = in_data + 8'd4;
    end
    assign array_read_out = my_unpacked_array[addr];
    always_comb begin
        if (addr == 2'd0) begin
            another_array[0] = in_data * 2;
            another_array[1] = 8'h0;
            another_array[2] = 8'h0;
            another_array[3] = 8'h0;
        end else if (addr == 2'd1) begin
            another_array[0] = 8'h0;
            another_array[1] = in_data / 2;
            another_array[2] = 8'h0;
            another_array[3] = 8'h0;
        end else begin
            another_array[0] = 8'h0;
            another_array[1] = 8'h0;
            another_array[2] = 8'h0;
            another_array[3] = 8'h0;
            another_array[addr] = in_data;
        end
    end
    always_comb begin
        for(int i=0; i<4; i++) begin
            copied_array[i] = my_unpacked_array[i];
        end
    end
    assign temp_another_array_read = another_array[addr];
    assign array_write_verify = temp_another_array_read + copied_array[0];
endmodule
module SignedUnsignedLogic (
    input  logic signed [7:0] signed_in1,
    input  logic signed [7:0] signed_in2,
    input  logic unsigned [7:0] unsigned_in1,
    input  logic unsigned [7:0] unsigned_in2,
    output logic signed [7:0] signed_out_add,
    output logic signed [7:0] signed_out_mul,
    output logic unsigned [7:0] unsigned_out_sub,
    output logic unsigned [7:0] unsigned_out_div
);
    logic signed [7:0] temp_signed_cast_val;
    logic unsigned [7:0] temp_unsigned_cast_val;
    logic signed [7:0] signed_const_expr;
    logic unsigned [7:0] unsigned_const_expr;
    assign temp_signed_cast_val = signed'(unsigned_in1);
    assign temp_unsigned_cast_val = unsigned'(signed_in1);
    assign signed_const_expr = -8'd10;
    assign unsigned_const_expr = 8'hFF;
    assign signed_out_add = (signed_in1 + signed_in2) + temp_signed_cast_val;
    assign signed_out_mul = (signed_in1 * signed_in2) + signed_const_expr;
    assign unsigned_out_sub = (unsigned_in1 - unsigned_in2) + temp_unsigned_cast_val;
    assign unsigned_out_div = (unsigned_in1 / unsigned_in2) + unsigned_const_expr;
endmodule
module ComplexExpressions (
    input logic [7:0] op1,
    input logic [7:0] op2,
    input logic [7:0] op3,
    input logic [7:0] op4,
    output logic [7:0] res_expr1,
    output logic [7:0] res_expr2,
    output logic [7:0] res_expr3
);
    logic [7:0] common_subexpr;
    logic [7:0] nested_op_a;
    logic [7:0] nested_op_b;
    logic [7:0] deeply_nested_conditional;
    logic [7:0] simplified_conditional_val;
    assign common_subexpr = (op1 + op2) * op3;
    assign deeply_nested_conditional = (op1 > op2) ?
                                       ((op3 == op4) ? (op1 * op3) : (op2 + op4)) :
                                       ((op1 < op3) ? (op2 / op1) : (op4 % op3));
    assign res_expr1 = (common_subexpr - op4) + deeply_nested_conditional;
    assign simplified_conditional_val = (op1 > op2) ? (op3 + op4) : (op3 + op4);
    assign res_expr2 = (common_subexpr + op1) + simplified_conditional_val;
    assign nested_op_a = (op1 & op2) | (op3 ^ op4);
    assign nested_op_b = ~(op1 | op2) ^ (op3 & op4);
    assign res_expr3 = nested_op_a + nested_op_b;
endmodule
module FunctionTaskModule (
    input logic [7:0] arg1,
    input logic [7:0] arg2,
    output logic [7:0] func_result,
    output logic [7:0] task_result
);
    function automatic logic [7:0] my_function (logic [7:0] f_in1, logic [7:0] f_in2);
        logic [7:0] temp_func_var;
        temp_func_var = f_in1 + f_in2;
        my_function = temp_func_var * 2;
    endfunction
    task automatic my_task (input logic [7:0] t_in1, input logic [7:0] t_in2, output logic [7:0] t_out);
        logic [7:0] temp_task_var;
        temp_task_var = t_in1 - t_in2;
        t_out = temp_task_var / 2;
    endtask
    class MyData;
        rand logic [7:0] val1;
        logic [7:0] val2;
        function new();
            val1 = 8'h11;
            val2 = 8'h22;
        endfunction
        function logic [7:0] sum_vals();
            return val1 + val2;
        endfunction
    endclass
    function automatic logic [7:0] get_sum_from_class();
        MyData my_object;
        my_object = new();
        return my_object.sum_vals();
    endfunction
    logic [7:0] temp_func_result;
    logic [7:0] temp_task_result_from_task;
    logic [7:0] temp_task_result_final;
    logic [7:0] class_sum_out;
    assign temp_func_result = my_function(arg1, arg2);
    always_comb begin
        my_task(arg1, arg2, temp_task_result_from_task);
    end
    always_comb begin
        logic [7:0] local_block_var;
        local_block_var = arg1 | arg2;
        temp_task_result_final = temp_task_result_from_task + local_block_var;
    end
    assign task_result = temp_task_result_final;
    assign class_sum_out = get_sum_from_class();
    assign func_result = temp_func_result + class_sum_out;
endmodule
