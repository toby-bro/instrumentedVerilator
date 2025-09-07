module case_priority_casex_complex_mod (
    input logic [1:0] case_expr,
    input logic [3:0] case_inside_val,
    output logic [4:0] internal_out
);
    always @* begin
        priority casex ({case_expr, case_inside_val[1:0]})
            4'b1???: internal_out = 24;
            4'b?1??: internal_out = 25;  
            4'b??1?: internal_out = 26;  
            4'b???1: internal_out = 27;  
            4'b0000: internal_out = 28;  
            default: internal_out = 29;
        endcase
    end
endmodule

module invalid_this_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module macro_concat_user (
    input logic [3:0] concat_in,
    output logic [7:0] concat_out
);
    `define MAKE_NAME(a,b) a``b
    logic var_signal;
    always_comb begin
        `MAKE_NAME(var,_signal) = concat_in[0];
    end
    assign concat_out = {4'b0, concat_in[3:1], var_signal};
endmodule

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module split_multiple_in_branch (
    input logic clk_j,
    input logic condition_j,
    input logic [7:0] in_a_j,
    input logic [7:0] in_b_j,
    output logic [7:0] out_x_j,
    output logic [7:0] out_y_j
);
    always @(posedge clk_j) begin
        if (condition_j) begin
            out_x_j <= in_a_j * 3;
            out_y_j <= in_b_j + 1;
        end else begin
            out_x_j <= in_a_j;
            out_y_j <= in_b_j;
        end
    end
endmodule

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module bind_directive_top (
    input logic i_clk,
    input logic [3:0] i_control,
    input logic [7:0] i_data,
    output logic [7:0] o_result,
    output logic o_status
);
    target_module_for_bind target_inst(
        .i_target_clk   (i_clk),
        .i_target_data  (i_data),
        .o_target_result(o_result)
    );
    module_to_bind bind_inst(
        .i_bind_clk     (i_clk),
        .i_bind_control (i_control),
        .o_bind_status  (o_status)
    );
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_a_1755007766248_965,
    input logic [3:0] inj_b_1755007766248_729,
    input logic [1:0] inj_case_expr_1755007766249_20,
    input logic inj_i_1755007766248_824,
    input logic [7:0] inj_in2_a_1755007766248_768,
    input wire [7:0] inj_in_array_data_1755007766254_418,
    input logic [2:0] inj_in_val_1755007766249_409,
    input int inj_in_val_1755007766251_7,
    input wire [1:0] inj_select_idx_1755007766254_282,
    input wire reset,
    output logic [7:0] inj_concat_out_1755007766262_560,
    output logic [7:0] inj_data_out_1755007766250_882,
    output logic inj_data_out_1755007766267_74,
    output logic [4:0] inj_internal_out_1755007766249_797,
    output logic [4:0] inj_internal_out_1755007766265_929,
    output logic inj_o_1755007766248_732,
    output logic [7:0] inj_o_result_1755007766249_314,
    output logic inj_o_status_1755007766249_947,
    output logic [7:0] inj_o_target_result_1755007766271_620,
    output logic [7:0] inj_out2_a_1755007766248_688,
    output logic inj_out_bit_1755007766253_543,
    output logic [7:0] inj_out_case_a_1755007766251_643,
    output logic [7:0] inj_out_case_b_1755007766251_46,
    output wire [3:0] inj_out_element_1755007766254_108,
    output logic [3:0] inj_out_part_1755007766258_559,
    output logic [7:0] inj_out_reg_1755007766258_306,
    output reg inj_out_res_1755007766249_248,
    output int inj_out_val_1755007766251_460,
    output logic [7:0] inj_out_x_j_1755007766256_656,
    output logic [7:0] inj_out_y_j_1755007766256_960,
    output logic inj_q_1755007766260_211,
    output logic [3:0] inj_sum_1755007766248_126
);
    // BEGIN: another_module_config_dummy_ts1755007766248
    // BEGIN: CombinationalLogicImplicit_ts1755007766248
    // BEGIN: split_basic_nonblocking_ts1755007766248
    // BEGIN: casez_xz_alt_ts1755007766249
    // BEGIN: sequential_register_en_ts1755007766250
    // BEGIN: mod_split_case_ts1755007766252
    logic [7:0]  split_case_var_ts1755007766252;
    logic [7:0] other_case_var_ts1755007766252;
        // BEGIN: unpacked_array_module_ts1755007766255
        logic [3:0] data_array_ts1755007766255 [4];
            // BEGIN: module_assignments_in_loops_ts1755007766258
            localparam int PART_START = 4;
            localparam int PART_WIDTH = 4;
            logic [7:0] reg_var_ts1755007766258;
            logic [3:0] part_var_ts1755007766258;
                target_module_for_bind target_module_for_bind_inst_1755007766271_8921 (
                    .o_target_result(inj_o_target_result_1755007766271_620),
                    .i_target_clk(clk),
                    .i_target_data(split_case_var_ts1755007766252)
                );
                // BEGIN: child_scalar_port_ts1755007766268
                assign inj_data_out_1755007766267_74 = inj_i_1755007766248_824;
                // END: child_scalar_port_ts1755007766268

                // BEGIN: case_priority_overlapping_mod_ts1755007766265
                always @* begin
                    priority casez (inj_case_expr_1755007766249_20)
                        2'b1?: inj_internal_out_1755007766265_929 = 5;
                        2'b?1: inj_internal_out_1755007766265_929 = 6;  
                        2'b0?: inj_internal_out_1755007766265_929 = 7;
                        2'b?0: inj_internal_out_1755007766265_929 = 8;  
                        default: inj_internal_out_1755007766265_929 = 9;
                    endcase
                end
                // END: case_priority_overlapping_mod_ts1755007766265

                macro_concat_user macro_concat_user_inst_1755007766262_6942 (
                    .concat_out(inj_concat_out_1755007766262_560),
                    .concat_in(data_array_ts1755007766255)
                );
                // BEGIN: mod_seq_reg_ts1755007766260
                always_ff @(posedge clk) begin
                    inj_q_1755007766260_211 <= inj_i_1755007766248_824;
                end
                // END: mod_seq_reg_ts1755007766260

            always_comb begin
                reg_var_ts1755007766258  = inj_in2_a_1755007766248_768;
                part_var_ts1755007766258 = 4'h0;
                for (int i = 0; i < 4; i++) begin
                    reg_var_ts1755007766258  = reg_var_ts1755007766258 + i;
                    reg_var_ts1755007766258 += (i * 2);
                    reg_var_ts1755007766258 <<= inj_in_val_1755007766249_409;
                    reg_var_ts1755007766258[i % 8] = (reg_var_ts1755007766258[i % 8] == 1'b0);
                    reg_var_ts1755007766258[PART_START +: PART_WIDTH] = i[3:0];
                end
                part_var_ts1755007766258 = reg_var_ts1755007766258[7:4];
            end
            assign inj_out_reg_1755007766258_306  = reg_var_ts1755007766258;
            assign inj_out_part_1755007766258_559 = part_var_ts1755007766258;
            // END: module_assignments_in_loops_ts1755007766258

            split_multiple_in_branch split_multiple_in_branch_inst_1755007766256_9950 (
                .out_y_j(inj_out_y_j_1755007766256_960),
                .clk_j(clk),
                .condition_j(inj_i_1755007766248_824),
                .in_a_j(other_case_var_ts1755007766252),
                .in_b_j(split_case_var_ts1755007766252),
                .out_x_j(inj_out_x_j_1755007766256_656)
            );
        always @(*) begin
            data_array_ts1755007766255[0] = inj_in_array_data_1755007766254_418[3:0];
            data_array_ts1755007766255[1] = inj_in_array_data_1755007766254_418[7:4];
            data_array_ts1755007766255[2] = 4'd8;
            data_array_ts1755007766255[3] = 4'd12;
        end
        assign inj_out_element_1755007766254_108 = data_array_ts1755007766255[inj_select_idx_1755007766254_282];
        // END: unpacked_array_module_ts1755007766255

        // BEGIN: recursive_macro_dummy_ts1755007766253
        `define RECURSIVE_TEST `RECURSIVE_TEST
        assign inj_out_bit_1755007766253_543 = inj_i_1755007766248_824;
        // END: recursive_macro_dummy_ts1755007766253

    always_comb begin
        split_case_var_ts1755007766252 = 8'hFF;
        other_case_var_ts1755007766252 = 8'hAA;
        case (inj_case_expr_1755007766249_20)
            2'b00: begin
                split_case_var_ts1755007766252 = inj_in2_a_1755007766248_768 + 5;
                other_case_var_ts1755007766252 = inj_in2_a_1755007766248_768 + 6;
            end
            2'b01: begin
                split_case_var_ts1755007766252 = inj_in2_a_1755007766248_768 - 5;
                other_case_var_ts1755007766252 = inj_in2_a_1755007766248_768 - 6;
            end
            default: begin
                split_case_var_ts1755007766252 = inj_in2_a_1755007766248_768;
                other_case_var_ts1755007766252 = inj_in2_a_1755007766248_768;
            end
        endcase
        inj_out_case_a_1755007766251_643 = split_case_var_ts1755007766252;
        inj_out_case_b_1755007766251_46 = other_case_var_ts1755007766252;
    end
    // END: mod_split_case_ts1755007766252

    invalid_this_diag_mod invalid_this_diag_mod_inst_1755007766251_9042 (
        .out_val(inj_out_val_1755007766251_460),
        .in_val(inj_in_val_1755007766251_7)
    );
    always_ff @(posedge clk) begin
        if (inj_i_1755007766248_824) begin
            inj_data_out_1755007766250_882 <= inj_in2_a_1755007766248_768;
        end
    end
    // END: sequential_register_en_ts1755007766250

    bind_directive_top bind_directive_top_inst_1755007766249_2822 (
        .i_clk(clk),
        .i_control(inj_a_1755007766248_965),
        .i_data(inj_in2_a_1755007766248_768),
        .o_result(inj_o_result_1755007766249_314),
        .o_status(inj_o_status_1755007766249_947)
    );
    always_comb begin
        inj_out_res_1755007766249_248 = 1'b0;
        casez (inj_in_val_1755007766249_409)
            3'b1?z: inj_out_res_1755007766249_248 = 1'b1;
            3'b0z?: inj_out_res_1755007766249_248 = 1'b0;
            default: inj_out_res_1755007766249_248 = 1'b1;
        endcase
    end
    // END: casez_xz_alt_ts1755007766249

    case_priority_casex_complex_mod case_priority_casex_complex_mod_inst_1755007766249_6011 (
        .case_inside_val(inj_a_1755007766248_965),
        .internal_out(inj_internal_out_1755007766249_797),
        .case_expr(inj_case_expr_1755007766249_20)
    );
    always @(posedge clk) begin
        inj_out2_a_1755007766248_688 <= inj_in2_a_1755007766248_768;
    end
    // END: split_basic_nonblocking_ts1755007766248

    always @* begin
        inj_sum_1755007766248_126 = inj_a_1755007766248_965 + inj_b_1755007766248_729;
    end
    // END: CombinationalLogicImplicit_ts1755007766248

    assign inj_o_1755007766248_732 = inj_i_1755007766248_824 & inj_i_1755007766248_824; 
    // END: another_module_config_dummy_ts1755007766248
endmodule

