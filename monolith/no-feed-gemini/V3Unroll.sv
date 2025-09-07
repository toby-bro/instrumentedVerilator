module UnrollGenFor_Simple (
    input logic [3:0] in_a,
    output logic [7:0] out_sum
);
    genvar i;
    logic [7:0] temp_sum;
    assign temp_sum = 8'h0;
    generate
        for (i = 0; i < 4; i = i + 1) begin : my_gen_block
            assign temp_sum = temp_sum + (in_a + i);
        end
    endgenerate
    assign out_sum = temp_sum;
endmodule
module UnrollWhile_Basic (
    input logic [3:0] in_data,
    output logic [7:0] out_result
);
    logic [7:0] local_sum;
    integer j;
    always_comb begin
        local_sum = 0;
        j = 0; 
        while (j < 3) begin 
            local_sum = local_sum + (in_data + j);
            j = j + 1; 
        end
        out_result = local_sum;
    end
endmodule
module UnrollGenFor_PragmaFull (
    input logic [3:0] in_val,
    output logic [15:0] out_accum
);
    genvar k;
    logic [15:0] current_accum;
    assign current_accum = 16'h0;
    generate
        for (k = 0; k < 5; k = k + 1) begin : pragma_full_block
            assign current_accum = current_accum + (in_val * k) + (in_val << k) + (k * 2);
            assign current_accum = current_accum + 1;
        end
    endgenerate
    assign out_accum = current_accum;
endmodule
module UnrollGenFor_PragmaDisable (
    input logic [3:0] in_input,
    output logic [7:0] out_final
);
    genvar m;
    logic [7:0] temp_val;
    assign temp_val = 8'h0;
    generate
        for (m = 0; m < 100; m = m + 1) begin : pragma_disable_block
            assign temp_val = temp_val + (in_input % 5);
        end
    endgenerate
    assign out_final = temp_val;
endmodule
module UnrollGenFor_LargeBody (
    input logic [3:0] in_data_a,
    input logic [3:0] in_data_b,
    output logic [15:0] out_complex_sum
);
    genvar n;
    logic [15:0] result_reg;
    assign result_reg = 16'h0;
    generate
        for (n = 0; n < 3; n = n + 1) begin : large_body_gen
            assign result_reg = result_reg + (in_data_a * n);
            assign result_reg = result_reg + (in_data_b << n);
            assign result_reg = result_reg + (n * n);
            assign result_reg = result_reg + n;
            assign result_reg = result_reg + in_data_a;
            assign result_reg = result_reg + in_data_b;
            assign result_reg = result_reg + 1;
        end
    endgenerate
    assign out_complex_sum = result_reg;
endmodule
module UnrollGenFor_VarReassign (
    input logic [3:0] in_val_v,
    output logic [7:0] out_sum_v
);
    genvar p;
    logic [7:0] sum_v;
    assign sum_v = 8'h0;
    generate
        for (p = 0; p < 4; p = p + 1) begin : reassign_var_gen
            assign sum_v = sum_v + in_val_v;
            if (in_val_v > 0) p = p + 1;
        end
    endgenerate
    assign out_sum_v = sum_v;
endmodule
module UnrollGenFor_ForkJoinNone (
    input logic [3:0] in_f,
    output logic [7:0] out_f
);
    genvar q;
    logic [7:0] sum_f;
    logic [3:0] sub_f;
    assign sum_f = 8'h0;
    assign sub_f = 4'h0;
    generate
        for (q = 0; q < 2; q = q + 1) begin : fork_gen
            always_comb begin
                fork : my_fork_block
                    begin
                        sum_f = sum_f + in_f;
                    end
                    begin
                        sub_f = sub_f + q;
                    end
                join_none
            end
        end
    endgenerate
    assign out_f = sum_f + sub_f;
endmodule
module UnrollWhile_NonConstant (
    input logic [3:0] in_limit,
    input logic [3:0] in_step,
    output logic [7:0] out_res
);
    logic [7:0] total_val;
    integer r;
    always_comb begin
        total_val = 0;
        r = 0;
        while (r < in_limit) begin 
            total_val = total_val + r;
            r = r + in_step; 
        end
        out_res = total_val;
    end
endmodule
module UnrollGenFor_CondZero (
    input logic [3:0] in_dummy,
    output logic [7:0] out_dummy
);
    genvar s;
    logic [7:0] unused_val;
    assign unused_val = 8'h0;
    generate
        for (s = 0; s < 0; s = s + 1) begin : zero_cond_gen
            assign unused_val = in_dummy + s;
        end
    endgenerate
    assign out_dummy = unused_val + in_dummy;
endmodule
module NestedGenvarLoop (
    input logic [3:0] in_x,
    output logic [15:0] out_matrix_sum
);
    genvar i_nest, j_nest;
    logic [15:0] total_nest_sum;
    assign total_nest_sum = 16'h0;
    generate
        for (i_nest = 0; i_nest < 2; i_nest = i_nest + 1) begin : outer_loop
            for (j_nest = 0; j_nest < 3; j_nest = j_nest + 1) begin : inner_loop
                assign total_nest_sum = total_nest_sum + (in_x + i_nest * 10 + j_nest);
            end
        end
    endgenerate
    assign out_matrix_sum = total_nest_sum;
endmodule
module UnrollGenFor_LocalparamBounds (
    input logic [3:0] in_base,
    output logic [7:0] out_final_val
);
    localparam int MY_LIMIT = 3;
    genvar idx;
    logic [7:0] current_val;
    assign current_val = 8'h0;
    generate
        for (idx = 0; idx < MY_LIMIT; idx = idx + 1) begin : lp_gen
            assign current_val = current_val + (in_base + idx);
        end
    endgenerate
    assign out_final_val = current_val;
endmodule
module UnrollGenFor_NegativeStep (
    input logic [3:0] in_start,
    output logic [7:0] out_down_sum
);
    genvar step_idx;
    logic [7:0] down_sum;
    assign down_sum = 8'h0;
    generate
        for (step_idx = 5; step_idx >= 0; step_idx = step_idx - 2) begin : neg_step_gen
            assign down_sum = down_sum + (in_start + step_idx);
        end
    endgenerate
    assign out_down_sum = down_sum;
endmodule
module UnrollWhile_ImplicitInc (
    input logic [3:0] in_val,
    output logic [7:0] out_implicit_sum
);
    logic [7:0] current_sum;
    integer iter;
    always_comb begin
        current_sum = 0;
        iter = 1;
        while (iter < 4) begin
            current_sum = current_sum + (in_val * iter);
            iter = iter + 1;
        end
        out_implicit_sum = current_sum;
    end
endmodule
