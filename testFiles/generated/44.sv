interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module case_single_default_after_item (
    input logic [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b01: out_res = 1'b1;
            default: out_res = 1'b0;
            2'b10: out_res = 1'b1;
        endcase
    end
endmodule

module mod_part_select (
    input wire [31:0] data_in,
    output logic [31:0] data_out
);
    logic [31:0] temp_reg;
    always_comb begin
        temp_reg[7:0] = data_in[7:0];
        temp_reg[15:8] = data_in[23:16];
        temp_reg[31:16] = data_in[15:0];
        temp_reg[0] = data_in[31];
        temp_reg[8] = data_in[0];
        data_out = temp_reg;
    end
endmodule

module mod_split_nested (
    input logic clk,
    input logic cond1,
    input logic cond2,
    input logic [7:0] data_in,
    input logic reset,
    output logic [7:0] out_nested_a,
    output logic [7:0] out_nested_b
);
    logic [7:0]  split_nested_var;
    logic [7:0] other_nested_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_nested_var <= 8'b0;
            other_nested_var <= 8'b0;
        end else begin
            split_nested_var <= 8'h11; 
            other_nested_var <= 8'h22; 
            if (cond1) begin
                split_nested_var <= data_in + 10;
                other_nested_var <= data_in + 20;
                if (cond2) begin
                    split_nested_var <= data_in + 100;
                    other_nested_var <= data_in + 200;
                end
            end else begin
                split_nested_var <= data_in - 10;
                other_nested_var <= data_in - 20;
            end
        end
    end
    always_comb begin
        out_nested_a = split_nested_var;
        out_nested_b = other_nested_var;
    end
endmodule

module module_in_program_ref (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module module_simple (
    input wire i_a,
    input wire i_b,
    output wire o_c
);
    wire internal_xor_res;
    assign internal_xor_res = i_a ^ i_b;
    assign o_c = internal_xor_res & i_a;
endmodule

module module_using_package_param (
    input logic [31:0] wide_data_in,
    output logic [31:0] wide_data_out
);
    assign wide_data_out = wide_data_in;
endmodule

module module_assign_nonblocking (
    input logic clk,
    input logic [7:0] in_value,
    input logic reset,
    output logic out_data_q
);
    my_if vif_inst();
    logic [7:0] data_q;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            vif_inst.data <= 8'h0;
            data_q <= 8'h0;
        end else begin
            vif_inst.data <= in_value;
            data_q <= vif_inst.data;
        end
    end
    assign out_data_q = data_q;
endmodule

module nested_blocks (
    input logic data_value,
    input logic level1_en,
    input logic level2_en,
    output logic result_out
);
    always_comb begin : main_block 
        result_out = 1'b0; 
        if (level1_en) begin : inner_block1 
            if (level2_en) begin : inner_block2 
                result_out = data_value;
            end 
        end 
    end
endmodule

module primitive_example (
    input logic i_p1,
    input logic i_p2,
    output logic o_p_and,
    output logic o_p_xor
);
    and (o_p_and, i_p1, i_p2);
    xor (o_p_xor, i_p1, i_p2);
endmodule

module range_select_simple_packed (
    input logic [15:0] in_vec,
    output logic [7:0] out_slice_be,
    output logic [7:0] out_slice_le
);
    assign out_slice_be = in_vec[7:0]; 
    assign out_slice_le = in_vec[7:0]; 
endmodule

module split_vector_assign (
    input logic clk_y,
    input logic condition_y,
    input logic [7:0] in_val_y,
    output logic [7:0] out_vec_y
);
    always @(posedge clk_y) begin
        if (condition_y) begin
            out_vec_y[3:0] <= in_val_y[3:0];
            out_vec_y[7:4] <= in_val_y[7:4] + 1;
        end else begin
            out_vec_y <= 8'hFF;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_cond1_1755004218200_325,
    input logic inj_cond2_1755004218200_562,
    input logic [7:0] inj_data_in_1755004218200_923,
    input wire [31:0] inj_data_in_1755004218261_800,
    input logic [3:0] inj_data_in_n_1755004218204_36,
    input int inj_in_val_1755004218200_371,
    input logic [1:0] inj_in_val_1755004218205_801,
    input logic [7:0] inj_op1_v_1755004218207_723,
    input logic [15:0] inj_packed_in_1755004218201_844,
    input logic [2:0] inj_shamt_1755004218210_439,
    input int inj_val_b_1755004218202_545,
    input int inj_val_c_1755004218202_927,
    input logic [31:0] inj_wide_data_in_1755004218199_577,
    input wire reset,
    output logic inj_comb_out_1755004218218_388,
    output logic [3:0] inj_data_out1_n_1755004218204_935,
    output logic [3:0] inj_data_out2_n_1755004218204_617,
    output logic [31:0] inj_data_out_1755004218261_659,
    output logic [7:0] inj_diff_v_1755004218207_302,
    output logic [7:0] inj_field2_o_1755004218201_231,
    output logic [5:0] inj_indicators_1755004218202_629,
    output logic [4:0] inj_internal_out_1755004218215_920,
    output logic [4:0] inj_internal_out_1755004218229_712,
    output logic [7:0] inj_left_shift_1755004218210_329,
    output wire inj_o_c_1755004218241_683,
    output logic inj_o_p_and_1755004218237_486,
    output logic inj_o_p_and_1755004218245_722,
    output logic inj_o_p_xor_1755004218237_901,
    output logic inj_o_p_xor_1755004218245_914,
    output logic inj_o_reg_out_1755004218200_540,
    output wire inj_o_wire_out_1755004218200_957,
    output logic [15:0] inj_out_1755004218222_516,
    output logic [7:0] inj_out_a_1755004218213_402,
    output logic [7:0] inj_out_b_1755004218213_508,
    output logic inj_out_data_q_1755004218209_267,
    output logic [7:0] inj_out_nested_a_1755004218200_572,
    output logic [7:0] inj_out_nested_b_1755004218200_688,
    output reg inj_out_res_1755004218205_92,
    output logic [7:0] inj_out_slice_be_1755004218226_513,
    output logic [7:0] inj_out_slice_le_1755004218226_244,
    output int inj_out_val_1755004218200_281,
    output logic [7:0] inj_out_vec_1755004218256_202,
    output logic [7:0] inj_out_vec_y_1755004218201_802,
    output logic [7:0] inj_prod_v_1755004218207_996,
    output logic inj_result_out_1755004218250_580,
    output logic [7:0] inj_right_shift_arith_1755004218210_530,
    output logic [7:0] inj_right_shift_logic_1755004218210_53,
    output logic inj_seq_out_1755004218218_521,
    output logic [7:0] inj_sum_v_1755004218207_438,
    output logic inj_tok_out_1755004218233_257,
    output logic inj_udnt_output_1755004218266_387,
    output logic inj_uout_1755004218266_704,
    output logic [31:0] inj_wide_data_out_1755004218199_286
);
    // BEGIN: nets_alias_clocking_ts1755004218200
    wire  w_internal_ts1755004218200;
    logic r_internal_ts1755004218200;
        // BEGIN: split_multiple_blocking_ts1755004218204
        logic [3:0] temp_n_ts1755004218204;
            // BEGIN: mod_split_comb_ts1755004218213
            logic [7:0]  split_comb_var_ts1755004218213;
            logic [7:0] other_comb_var_ts1755004218213;
                // BEGIN: MixedLogic_ts1755004218218
                logic seq_reg_ts1755004218218;
                logic comb_intermediate_ts1755004218218;
                    // BEGIN: udnt_port_module_ts1755004218266
                    assign inj_uout_1755004218266_704 = inj_cond1_1755004218200_325;
                    assign inj_udnt_output_1755004218266_387 = inj_cond2_1755004218200_562;
                    // END: udnt_port_module_ts1755004218266

                    mod_part_select mod_part_select_inst_1755004218261_2229 (
                        .data_in(inj_data_in_1755004218261_800),
                        .data_out(inj_data_out_1755004218261_659)
                    );
                    // BEGIN: SimpleLoopExample_ts1755004218256
                    always_comb begin
                        for (int i = 0; i < 8; i++) begin
                            inj_out_vec_1755004218256_202[i] = other_comb_var_ts1755004218213[7 - i];
                        end
                    end
                    // END: SimpleLoopExample_ts1755004218256

                    nested_blocks nested_blocks_inst_1755004218250_6935 (
                        .level1_en(r_internal_ts1755004218200),
                        .level2_en(seq_reg_ts1755004218218),
                        .result_out(inj_result_out_1755004218250_580),
                        .data_value(inj_cond2_1755004218200_562)
                    );
                    // BEGIN: primitive_example_ts1755004218245
                    and (inj_o_p_and_1755004218245_722, seq_reg_ts1755004218218, comb_intermediate_ts1755004218218);
                    xor (inj_o_p_xor_1755004218245_914, seq_reg_ts1755004218218, comb_intermediate_ts1755004218218);
                    // END: primitive_example_ts1755004218245

                    module_simple module_simple_inst_1755004218241_2846 (
                        .i_a(clk),
                        .i_b(w_internal_ts1755004218200),
                        .o_c(inj_o_c_1755004218241_683)
                    );
                    primitive_example primitive_example_inst_1755004218237_4693 (
                        .i_p2(inj_cond2_1755004218200_562),
                        .o_p_and(inj_o_p_and_1755004218237_486),
                        .o_p_xor(inj_o_p_xor_1755004218237_901),
                        .i_p1(inj_cond1_1755004218200_325)
                    );
                    // BEGIN: Module_MacroTokens_ts1755004218233
                    `define PASTE(a,b) a``b
                    logic `PASTE(my,_var);
                    always_comb begin
                        `PASTE(my,_var) = r_internal_ts1755004218200;
                        inj_tok_out_1755004218233_257         = `PASTE(my,_var);
                    end
                    // END: Module_MacroTokens_ts1755004218233

                    // BEGIN: case_priority_overlapping_mod_ts1755004218229
                    always @* begin
                        priority casez (inj_in_val_1755004218205_801)
                            2'b1?: inj_internal_out_1755004218229_712 = 5;
                            2'b?1: inj_internal_out_1755004218229_712 = 6;  
                            2'b0?: inj_internal_out_1755004218229_712 = 7;
                            2'b?0: inj_internal_out_1755004218229_712 = 8;  
                            default: inj_internal_out_1755004218229_712 = 9;
                        endcase
                    end
                    // END: case_priority_overlapping_mod_ts1755004218229

                    range_select_simple_packed range_select_simple_packed_inst_1755004218226_2179 (
                        .out_slice_le(inj_out_slice_le_1755004218226_244),
                        .in_vec(inj_packed_in_1755004218201_844),
                        .out_slice_be(inj_out_slice_be_1755004218226_513)
                    );
                    // BEGIN: always_comb_assign_ts1755004218223
                    always_comb begin
                        inj_out_1755004218222_516 = inj_packed_in_1755004218201_844;
                    end
                    // END: always_comb_assign_ts1755004218223

                always @(posedge clk or negedge reset) begin
                    if (!reset) begin
                        seq_reg_ts1755004218218 <= 1'b0;
                    end else begin
                        seq_reg_ts1755004218218 <= inj_cond2_1755004218200_562;
                    end
                end
                assign inj_seq_out_1755004218218_521 = seq_reg_ts1755004218218;
                always @(seq_reg_ts1755004218218 or r_internal_ts1755004218200 or inj_cond1_1755004218200_325) begin
                    comb_intermediate_ts1755004218218 = (seq_reg_ts1755004218218 & r_internal_ts1755004218200) | (~seq_reg_ts1755004218218 & inj_cond1_1755004218200_325);
                end
                assign inj_comb_out_1755004218218_388 = comb_intermediate_ts1755004218218;
                // END: MixedLogic_ts1755004218218

                // BEGIN: case_priority_casex_complex_mod_ts1755004218215
                always @* begin
                    priority casex ({inj_in_val_1755004218205_801, inj_data_in_n_1755004218204_36[1:0]})
                        4'b1???: inj_internal_out_1755004218215_920 = 24;
                        4'b?1??: inj_internal_out_1755004218215_920 = 25;  
                        4'b??1?: inj_internal_out_1755004218215_920 = 26;  
                        4'b???1: inj_internal_out_1755004218215_920 = 27;  
                        4'b0000: inj_internal_out_1755004218215_920 = 28;  
                        default: inj_internal_out_1755004218215_920 = 29;
                    endcase
                end
                // END: case_priority_casex_complex_mod_ts1755004218215

            always_comb begin
                split_comb_var_ts1755004218213 = 8'b0; 
                other_comb_var_ts1755004218213 = 8'b0;
                if (r_internal_ts1755004218200) begin
                    split_comb_var_ts1755004218213 = inj_data_in_1755004218200_923;
                    other_comb_var_ts1755004218213 = inj_data_in_1755004218200_923 + 1;
                end
                inj_out_a_1755004218213_402 = split_comb_var_ts1755004218213;
                inj_out_b_1755004218213_508 = other_comb_var_ts1755004218213;
            end
            // END: mod_split_comb_ts1755004218213

            // BEGIN: shift_ops_ts1755004218211
            assign inj_left_shift_1755004218210_329 = inj_data_in_1755004218200_923 << inj_shamt_1755004218210_439;
            assign inj_right_shift_logic_1755004218210_53 = inj_data_in_1755004218200_923 >> inj_shamt_1755004218210_439;
            assign inj_right_shift_arith_1755004218210_530 = inj_data_in_1755004218200_923 >>> inj_shamt_1755004218210_439;
            // END: shift_ops_ts1755004218211

            module_assign_nonblocking module_assign_nonblocking_inst_1755004218209_5248 (
                .in_value(inj_op1_v_1755004218207_723),
                .reset(reset),
                .out_data_q(inj_out_data_q_1755004218209_267),
                .clk(clk)
            );
            // BEGIN: split_arith_nb_ts1755004218207
            always @(posedge clk) begin
                inj_sum_v_1755004218207_438 <= inj_op1_v_1755004218207_723 + inj_data_in_1755004218200_923;
                inj_diff_v_1755004218207_302 <= inj_op1_v_1755004218207_723 - inj_data_in_1755004218200_923;
                inj_prod_v_1755004218207_996 <= inj_op1_v_1755004218207_723 * inj_data_in_1755004218200_923;
            end
            // END: split_arith_nb_ts1755004218207

            case_single_default_after_item case_single_default_after_item_inst_1755004218205_636 (
                .in_val(inj_in_val_1755004218205_801),
                .out_res(inj_out_res_1755004218205_92)
            );
        always @(*) begin
            temp_n_ts1755004218204 = inj_data_in_n_1755004218204_36 + 1;
            inj_data_out1_n_1755004218204_935 = temp_n_ts1755004218204 * 2;
            inj_data_out2_n_1755004218204_617 = temp_n_ts1755004218204 + 3;
        end
        // END: split_multiple_blocking_ts1755004218204

        // BEGIN: dup_compare_ts1755004218203
        always_comb begin
            inj_indicators_1755004218202_629 = '0;
            inj_indicators_1755004218202_629[0] = (inj_in_val_1755004218200_371 == inj_val_b_1755004218202_545);
            inj_indicators_1755004218202_629[1] = (inj_in_val_1755004218200_371 != inj_val_b_1755004218202_545);
            inj_indicators_1755004218202_629[2] = (inj_in_val_1755004218200_371 > inj_val_b_1755004218202_545);
            inj_indicators_1755004218202_629[3] = (inj_in_val_1755004218200_371 < inj_val_b_1755004218202_545);
            inj_indicators_1755004218202_629[4] = (inj_in_val_1755004218200_371 >= inj_val_b_1755004218202_545);
            inj_indicators_1755004218202_629[5] = (inj_in_val_1755004218200_371 <= inj_val_b_1755004218202_545);
            if (inj_val_b_1755004218202_545 == inj_val_c_1755004218202_927) begin
                inj_indicators_1755004218202_629 = inj_indicators_1755004218202_629 | 6'b111111;
            end
            if (inj_in_val_1755004218200_371 > inj_val_c_1755004218202_927) begin
                inj_indicators_1755004218202_629 = inj_indicators_1755004218202_629 & 6'b000000;
            end
            if ((inj_in_val_1755004218200_371 < inj_val_b_1755004218202_545) && (inj_val_b_1755004218202_545 > inj_val_c_1755004218202_927)) begin
                inj_indicators_1755004218202_629[0] = 1;
            end else if ((inj_in_val_1755004218200_371 >= inj_val_b_1755004218202_545) || (inj_val_b_1755004218202_545 <= inj_val_c_1755004218202_927)) begin
                inj_indicators_1755004218202_629[1] = 1;
            end
        end
        // END: dup_compare_ts1755004218203

        split_vector_assign split_vector_assign_inst_1755004218201_153 (
            .condition_y(inj_cond1_1755004218200_325),
            .in_val_y(inj_data_in_1755004218200_923),
            .out_vec_y(inj_out_vec_y_1755004218201_802),
            .clk_y(clk)
        );
        // BEGIN: typedef_struct_public_mod_ts1755004218201
        typedef struct packed {
            logic [7:0] field1_ts1755004218201;
            logic [7:0] field2_ts1755004218201;
        } my_public_packed_struct_t;
        my_public_packed_struct_t my_struct_var;
        always_comb begin
            my_struct_var = inj_packed_in_1755004218201_844;
        end
        assign inj_field2_o_1755004218201_231 = my_struct_var.field2_ts1755004218201;
        // END: typedef_struct_public_mod_ts1755004218201

    assign w_internal_ts1755004218200  = clk & inj_cond2_1755004218200_562;
    assign inj_o_wire_out_1755004218200_957  = w_internal_ts1755004218200;
    always_ff @(posedge clk) r_internal_ts1755004218200 <= inj_cond1_1755004218200_325;
    assign inj_o_reg_out_1755004218200_540 = r_internal_ts1755004218200;
    // END: nets_alias_clocking_ts1755004218200

    module_in_program_ref module_in_program_ref_inst_1755004218200_9431 (
        .in_val(inj_in_val_1755004218200_371),
        .out_val(inj_out_val_1755004218200_281)
    );
    mod_split_nested mod_split_nested_inst_1755004218200_3118 (
        .reset(reset),
        .out_nested_a(inj_out_nested_a_1755004218200_572),
        .out_nested_b(inj_out_nested_b_1755004218200_688),
        .clk(clk),
        .cond1(inj_cond1_1755004218200_325),
        .cond2(inj_cond2_1755004218200_562),
        .data_in(inj_data_in_1755004218200_923)
    );
    module_using_package_param module_using_package_param_inst_1755004218199_5587 (
        .wide_data_out(inj_wide_data_out_1755004218199_286),
        .wide_data_in(inj_wide_data_in_1755004218199_577)
    );
endmodule

