module unroll_basic_for (
    input logic [7:0] in_val,
    output logic [7:0] out_sum
);
    logic [7:0] temp_sum;
    always_comb begin
        temp_sum = 8'h00;
        for (int i = 0; i < 4; i++) begin
            temp_sum = temp_sum + in_val + i;
        end
        out_sum = temp_sum;
    end
endmodule
module unroll_large_body (
    input logic [7:0] in_data,
    output logic [7:0] out_result
);
    logic [7:0] temp_res;
    always_comb begin
        temp_res = 8'h01;
        for (int j = 0; j < 2; j++) begin
            temp_res = temp_res + in_data + j;
            temp_res = temp_res - (in_data >> 1);
            temp_res = temp_res + (in_data[0] ? 1 : 0);
            temp_res = temp_res * 2;
            temp_res = temp_res / 2;
            temp_res = temp_res & 8'hF0;
            temp_res = temp_res | 8'h0F;
            temp_res = temp_res ^ in_data;
            temp_res = temp_res + 1;
            temp_res = temp_res - 1;
            if (in_data > 10) begin
                temp_res = temp_res + 5;
            end else begin
                temp_res = temp_res - 5;
            end
            temp_res = temp_res << 1;
            temp_res = temp_res >> 1;
            temp_res = temp_res + 3;
            temp_res = temp_res - 3;
            temp_res = temp_res + 7;
            temp_res = temp_res - 7;
            temp_res = temp_res + 11;
            temp_res = temp_res - 11;
            temp_res = temp_res + 13;
            temp_res = temp_res - 13;
            temp_res = temp_res + 17;
            temp_res = temp_res - 17;
            temp_res = temp_res + 19;
            temp_res = temp_res - 19;
            temp_res = temp_res + 23;
            temp_res = temp_res - 23;
            temp_res = temp_res + 29;
            temp_res = temp_res - 29;
            temp_res = temp_res + 31;
            temp_res = temp_res - 31;
        end
        out_result = temp_res;
    end
endmodule
module unroll_large_iterations (
    input logic [3:0] in_start_iter,
    output logic [3:0] out_final_iter
);
    logic [3:0] counter_iter;
    always_comb begin
        counter_iter = in_start_iter;
        for (int k = 0; k < 200; k++) begin
            counter_iter = counter_iter + 1;
        end
        out_final_iter = counter_iter;
    end
endmodule
module unroll_loop_var_assigned_in_body (
    input logic [7:0] in_reset_val,
    output logic [7:0] out_accum
);
    logic [7:0] accumulator;
    always_comb begin
        accumulator = 8'h00;
        for (int m = 0; m < 5; m++) begin
            accumulator = accumulator + in_reset_val + m;
        end
        out_accum = accumulator;
    end
endmodule
module unroll_with_pragma_disable (
    input logic [7:0] in_data_p,
    output logic [7:0] out_data_p
);
    logic [7:0] temp_p;
    always_comb begin
        temp_p = 8'h00;
        for (int n = 0; n < 3; n++) begin
            temp_p = temp_p + in_data_p + n;
        end
        out_data_p = temp_p;
    end
endmodule
module unroll_gen_for_basic (
    input logic [7:0] in_gen_val,
    output logic [7:0] out_gen_sum
);
    logic [7:0] gen_sum_array [3:0];
    logic [7:0] final_gen_sum;
    generate
        for (genvar g = 0; g < 4; g++) begin : gen_block
            always_comb begin
                gen_sum_array[g] = in_gen_val + g;
            end
        end
    endgenerate
    always_comb begin
        final_gen_sum = gen_sum_array[0] + gen_sum_array[1] + gen_sum_array[2] + gen_sum_array[3];
        out_gen_sum = final_gen_sum;
    end
endmodule
module unroll_gen_for_zero_iterations (
    input logic [7:0] in_dummy_val,
    output logic [7:0] out_dummy_res
);
    logic [7:0] dummy_reg_zero [0:0];
    generate
        for (genvar p = 0; p < 0; p++) begin : zero_iterations_block
            always_comb begin
                dummy_reg_zero[0] = in_dummy_val + p;
            end
        end
    endgenerate
    always_comb begin
        dummy_reg_zero[0] = in_dummy_val; 
        out_dummy_res = dummy_reg_zero[0];
    end
endmodule
module unroll_gen_for_with_parameters (
    input logic [7:0] in_param_val,
    output logic [7:0] out_param_sum
);
    parameter START_IDX = 0;
    parameter END_IDX = 2;
    logic [7:0] param_sum_array [END_IDX-1:START_IDX];
    logic [7:0] final_param_sum;
    generate
        for (genvar i = START_IDX; i < END_IDX; i++) begin : param_gen_block
            always_comb begin
                param_sum_array[i] = in_param_val + i;
            end
        end
    endgenerate
    always_comb begin
        final_param_sum = 8'h00;
        for (int j = START_IDX; j < END_IDX; j++) begin
            final_param_sum = final_param_sum + param_sum_array[j];
        end
        out_param_sum = final_param_sum;
    end
endmodule
module unroll_for_non_const_initializer (
    input logic [7:0] in_init_val,
    output logic [7:0] out_final_val
);
    logic [7:0] temp_val;
    always_comb begin
        temp_val = 8'h00;
        for (int i = in_init_val; i < 5; i++) begin
            temp_val = temp_val + i;
        end
        out_final_val = temp_val;
    end
endmodule
module unroll_for_loop_var_modified_in_body_error (
    input logic [3:0] in_limit,
    output logic [3:0] out_val
);
    logic [3:0] acc;
    always_comb begin
        acc = 4'b0;
        for (int i = 0; i < in_limit; i = i + 1) begin
            acc = acc + 1;
            if (i == 1) begin
                i = 4'h0; 
            end
        end
        out_val = acc;
    end
endmodule
module unroll_genfor_non_genvar_loop_var (
    input logic [7:0] in_val,
    output logic [7:0] out_sum
);
    logic [7:0] arr_sum [1:0];
    logic [7:0] final_sum;
    generate
        for (int i = 0; i < 2; i++) begin : gen_blk
            always_comb begin
                arr_sum[i] = in_val + i;
            end
        end
    endgenerate
    always_comb begin
        final_sum = arr_sum[0] + arr_sum[1];
        out_sum = final_sum;
    end
endmodule
module unroll_for_genvar_loop_var (
    input logic [7:0] in_val,
    output logic [7:0] out_sum
);
    logic [7:0] current_sum;
    always_comb begin
        current_sum = 8'h00;
        for (genvar i = 0; i < 2; i++) begin
            current_sum = current_sum + in_val + i;
        end
        out_sum = current_sum;
    end
endmodule
