interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module casez_xz_alt (
    input logic [2:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            3'b1?z: out_res = 1'b1;
            3'b0z?: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module dup_literal_param (
    input logic [4:0] index,
    output logic [7:0] final_result
);
    parameter CONST_A = 8'd10;
    localparam CONST_B = 8'd20;
    parameter CONST_C = 10;
    localparam CONST_D = 8'hFF;
    parameter CONST_E = 8'b01010101;
    logic [7:0] temp1, temp2;
    assign temp1 = index + CONST_A;
    assign temp2 = index + 10;
    always_comb begin
        logic [7:0] local_temp;
        local_temp = index * CONST_B;
        final_result = temp1 + temp2 + local_temp;
        if (index > 5) begin
            final_result = final_result + 1;
        end else if (index < CONST_C) begin
            final_result = final_result - 1;
        end
        case (index)
            5'd0: final_result = CONST_A;
            5'd1: final_result = 20;
            5'd2: final_result = 10;
            5'd3: final_result = CONST_B;
            5'd4: final_result = CONST_D;
            5'd5: final_result = 8'hFF;
            default: final_result = CONST_E;
        endcase
    end
endmodule

module mod_split_case (
    input logic [7:0] data_in,
    input logic [1:0] sel,
    output logic [7:0] out_case_a,
    output logic [7:0] out_case_b
);
    logic [7:0]  split_case_var;
    logic [7:0] other_case_var;
    always_comb begin
        split_case_var = 8'hFF;
        other_case_var = 8'hAA;
        case (sel)
            2'b00: begin
                split_case_var = data_in + 5;
                other_case_var = data_in + 6;
            end
            2'b01: begin
                split_case_var = data_in - 5;
                other_case_var = data_in - 6;
            end
            default: begin
                split_case_var = data_in;
                other_case_var = data_in;
            end
        endcase
        out_case_a = split_case_var;
        out_case_b = other_case_var;
    end
endmodule

module multiplexer_2to1 (
    input logic data0,
    input logic data1,
    input logic sel,
    output logic result
);
    assign result = sel ? data1 : data0;
endmodule

module module_assign_blocking (
    input logic [7:0] in_data,
    output logic out_valid_status
);
    my_if vif_inst();
    always_comb begin
        vif_inst.data = in_data;
        vif_inst.valid = 1'b1;
        vif_inst.ready = 1'b0;
        out_valid_status = vif_inst.valid;
    end
endmodule

module split_seq_dependency (
    input logic clk_c,
    input logic [7:0] in_val_c,
    output logic [7:0] out_val_c
);
    logic [7:0] mid_val_c;
    always @(posedge clk_c) begin
        mid_val_c <= in_val_c + 1;
        out_val_c <= mid_val_c * 2;
    end
endmodule

module snippet #(
    parameter bit GEN = 1
) (
    input wire clk,
    input logic inj_data0_1755007782414_431,
    input logic inj_data1_1755007782414_10,
    input logic [15:0] inj_dividend_mod_1755007782462_652,
    input wire [1:0] inj_dtl_action_sel_1755007782422_182,
    input wire [7:0] inj_dtl_data_b_1755007782422_124,
    input bit [7:0] inj_in1_1755007782427_194,
    input bit [7:0] inj_in2_1755007782427_792,
    input logic [7:0] inj_in_data_1755007782416_701,
    input logic [2:0] inj_in_val_1755007782415_114,
    input int inj_in_val_1755007782417_535,
    input logic [15:0] inj_in_vector_1755007782431_151,
    input logic [4:0] inj_index_1755007782419_72,
    input logic inj_sel_1755007782414_831,
    input logic [1:0] inj_selector_1755007782414_700,
    input int inj_val_false_1755007782440_869,
    input wire reset,
    output logic [7:0] inj_dtl_result_reg_1755007782422_587,
    output logic inj_dummy_1755007782472_590,
    output logic inj_dummy_out_1755007782478_379,
    output logic [7:0] inj_final_result_1755007782419_67,
    output logic inj_o_1755007782415_323,
    output logic inj_o_out_1755007782416_637,
    output logic inj_o_out_1755007782420_436,
    output bit [7:0] inj_out1_1755007782427_210,
    output bit [7:0] inj_out2_1755007782427_896,
    output wire inj_out_1755007782436_309,
    output logic [7:0] inj_out_a_1755007782418_512,
    output logic [7:0] inj_out_b_1755007782418_334,
    output logic [7:0] inj_out_case_a_1755007782421_274,
    output logic [7:0] inj_out_case_b_1755007782421_787,
    output logic inj_out_data_pull0_1755007782452_274,
    output logic inj_out_data_pull1_1755007782452_188,
    output logic [7:0] inj_out_diff_m2_1755007782448_937,
    output reg inj_out_res_1755007782415_886,
    output logic [7:0] inj_out_slice_1755007782431_845,
    output int inj_out_val_1755007782417_617,
    output int inj_out_val_1755007782440_239,
    output logic [7:0] inj_out_val_c_1755007782466_623,
    output logic inj_out_valid_status_1755007782416_630,
    output logic [15:0] inj_quotient_1755007782462_771,
    output logic [7:0] inj_remainder_1755007782462_766,
    output logic inj_result_1755007782414_168,
    output logic [7:0] inj_selected_output_1755007782414_602,
    output logic inj_sig_out_1755007782444_25,
    output logic [7:0] inj_var_out_m2_1755007782448_350,
    output logic inj_y_1755007782457_123
);
    // BEGIN: generate_for_block_ts1755007782414
    wire [7:0] data_ts1755007782414 [3:0]; 
        // BEGIN: mod_split_comb_ts1755007782418
        logic [7:0]  split_comb_var_ts1755007782418;
        logic [7:0] other_comb_var_ts1755007782418;
            // BEGIN: name_conflict_example_ts1755007782420
            parameter int my_param = 5;
            logic my_var_ts1755007782420;
                // BEGIN: deep_task_logic_ts1755007782424
                task automatic perform_action;
                    input [7:0] in_a;
                    input [7:0] in_b;
                    input [1:0] action;
                    output logic [7:0] calculated_res_ts1755007782424;
                    logic [7:0] temp_task_calc_ts1755007782424;
                    if (action[0]) begin
                        if (action[1]) begin
                            temp_task_calc_ts1755007782424 = in_a + in_b;
                        end else begin
                            temp_task_calc_ts1755007782424 = in_a - in_b;
                        end
                    end else begin
                        if (action[1]) begin
                            temp_task_calc_ts1755007782424 = in_a & in_b;
                        end else begin
                            temp_task_calc_ts1755007782424 = in_a | in_b;
                        end
                    end
                    case (temp_task_calc_ts1755007782424[1:0])
                        2'b00: calculated_res_ts1755007782424 = temp_task_calc_ts1755007782424 ^ 8'hFF;
                        2'b01: calculated_res_ts1755007782424 = temp_task_calc_ts1755007782424 + 1;
                        2'b10: calculated_res_ts1755007782424 = temp_task_calc_ts1755007782424 - 1;
                        default: calculated_res_ts1755007782424 = temp_task_calc_ts1755007782424;
                    endcase
                endtask
                always_ff @(posedge clk or negedge reset) begin
                    if (!reset) begin
                        inj_dtl_result_reg_1755007782422_587 <= 8'd0;
                    end else begin
                        logic [7:0] next_dtl_result_ts1755007782424;
                            // BEGIN: expr_postsub_comb_ts1755007782448
                            logic [7:0] var_m2_ts1755007782448;
                                // BEGIN: mixed_conn_child_ts1755007782479
                                logic dummy_internal_ts1755007782479;
                                always_comb dummy_internal_ts1755007782479 = |next_dtl_result_ts1755007782424 | inj_sel_1755007782414_831;
                                assign inj_dummy_out_1755007782478_379 = dummy_internal_ts1755007782479;
                                // END: mixed_conn_child_ts1755007782479

                                // BEGIN: mod_err_event_constant_ts1755007782473
                                always @(posedge 1'b1) begin
                                    inj_dummy_1755007782472_590 = ~inj_dummy_1755007782472_590;
                                end
                                // END: mod_err_event_constant_ts1755007782473

                                split_seq_dependency split_seq_dependency_inst_1755007782466_543 (
                                    .out_val_c(inj_out_val_c_1755007782466_623),
                                    .clk_c(clk),
                                    .in_val_c(next_dtl_result_ts1755007782424)
                                );
                                // BEGIN: div_mod_ops_ts1755007782462
                                assign inj_quotient_1755007782462_771 = (inj_in_data_1755007782416_701 == 0) ? 16'hFFFF : (inj_in_vector_1755007782431_151 / inj_in_data_1755007782416_701); 
                                assign inj_remainder_1755007782462_766 = (split_comb_var_ts1755007782418 == 0) ? 8'hFF : (inj_dividend_mod_1755007782462_652 % split_comb_var_ts1755007782418);
                                // END: div_mod_ops_ts1755007782462

                                // BEGIN: mod_comb_logic_ts1755007782457
                                always_comb begin
                                    inj_y_1755007782457_123 = inj_data1_1755007782414_10 & my_var_ts1755007782420;
                                end
                                // END: mod_comb_logic_ts1755007782457

                                // BEGIN: module_with_unconnected_drive_ts1755007782453
                                assign inj_out_data_pull1_1755007782452_188 = my_var_ts1755007782420;
                                assign inj_out_data_pull0_1755007782452_274 = ~my_var_ts1755007782420;
                                // END: module_with_unconnected_drive_ts1755007782453

                            always_comb begin
                                var_m2_ts1755007782448 = other_comb_var_ts1755007782418;
                                inj_out_diff_m2_1755007782448_937 = (var_m2_ts1755007782448--) - next_dtl_result_ts1755007782424;
                                inj_var_out_m2_1755007782448_350 = var_m2_ts1755007782448;
                            end
                            // END: expr_postsub_comb_ts1755007782448

                            // BEGIN: GenerateIfParam_ts1755007782444
                            generate
                                if (GEN) begin : g_true
                                    assign inj_sig_out_1755007782444_25 = inj_sel_1755007782414_831;
                                end
                                else begin : g_false
                                    assign inj_sig_out_1755007782444_25 = ~inj_sel_1755007782414_831;
                                end
                            endgenerate
                            // END: GenerateIfParam_ts1755007782444

                            // BEGIN: ConditionalOps_ts1755007782440
                            assign inj_out_val_1755007782440_239 = my_var_ts1755007782420 ? inj_in_val_1755007782417_535 : inj_val_false_1755007782440_869;
                            // END: ConditionalOps_ts1755007782440

                            // BEGIN: Comb_Assign_ts1755007782436
                            assign inj_out_1755007782436_309 = clk & reset;
                            // END: Comb_Assign_ts1755007782436

                            // BEGIN: MiscExpressions_ValueRange_ts1755007782431
                            always_comb begin
                                inj_out_slice_1755007782431_845 = inj_in_vector_1755007782431_151[7:0];
                            end
                            // END: MiscExpressions_ValueRange_ts1755007782431

                            // BEGIN: comb_simple_ts1755007782428
                            always @* begin
                                inj_out1_1755007782427_210 = inj_in1_1755007782427_194 & inj_in2_1755007782427_792;
                                inj_out2_1755007782427_896 = inj_in1_1755007782427_194 | inj_in2_1755007782427_792;
                            end
                            // END: comb_simple_ts1755007782428

                        if (reset) begin
                            perform_action(data_ts1755007782414, inj_dtl_data_b_1755007782422_124, inj_dtl_action_sel_1755007782422_182, next_dtl_result_ts1755007782424);
                        end else begin
                            next_dtl_result_ts1755007782424 = inj_dtl_result_reg_1755007782422_587;
                        end
                        inj_dtl_result_reg_1755007782422_587 <= next_dtl_result_ts1755007782424;
                    end
                end
                // END: deep_task_logic_ts1755007782424

                mod_split_case mod_split_case_inst_1755007782421_9884 (
                    .data_in(inj_in_data_1755007782416_701),
                    .sel(inj_selector_1755007782414_700),
                    .out_case_a(inj_out_case_a_1755007782421_274),
                    .out_case_b(inj_out_case_b_1755007782421_787)
                );
            always_comb my_var_ts1755007782420 = inj_data1_1755007782414_10;
            assign inj_o_out_1755007782420_436 = inj_data1_1755007782414_10 && (my_param == 5) && my_var_ts1755007782420;
            // END: name_conflict_example_ts1755007782420

            dup_literal_param dup_literal_param_inst_1755007782419_5349 (
                .index(inj_index_1755007782419_72),
                .final_result(inj_final_result_1755007782419_67)
            );
        always_comb begin
            split_comb_var_ts1755007782418 = 8'b0; 
            other_comb_var_ts1755007782418 = 8'b0;
            if (inj_data1_1755007782414_10) begin
                split_comb_var_ts1755007782418 = inj_in_data_1755007782416_701;
                other_comb_var_ts1755007782418 = inj_in_data_1755007782416_701 + 1;
            end
            inj_out_a_1755007782418_512 = split_comb_var_ts1755007782418;
            inj_out_b_1755007782418_334 = other_comb_var_ts1755007782418;
        end
        // END: mod_split_comb_ts1755007782418

        // BEGIN: simple_undeclared_mod_ts1755007782417
        assign inj_out_val_1755007782417_617 = inj_in_val_1755007782417_535;
        // END: simple_undeclared_mod_ts1755007782417

        // BEGIN: configuration_top_ts1755007782416
        assign inj_o_out_1755007782416_637 = inj_sel_1755007782414_831;
        // END: configuration_top_ts1755007782416

        module_assign_blocking module_assign_blocking_inst_1755007782416_7249 (
            .in_data(inj_in_data_1755007782416_701),
            .out_valid_status(inj_out_valid_status_1755007782416_630)
        );
        casez_xz_alt casez_xz_alt_inst_1755007782415_487 (
            .in_val(inj_in_val_1755007782415_114),
            .out_res(inj_out_res_1755007782415_886)
        );
        // BEGIN: top_module_config_dummy_ts1755007782415
        assign inj_o_1755007782415_323 = inj_data0_1755007782414_431; 
        // END: top_module_config_dummy_ts1755007782415

    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : data_gen
            assign data_ts1755007782414[i] = 8'(i + 1) * 8'(i + 1);
        end
    endgenerate
    always_comb begin
        case (inj_selector_1755007782414_700)
            0: inj_selected_output_1755007782414_602 = data_ts1755007782414[0];
            1: inj_selected_output_1755007782414_602 = data_ts1755007782414[1];
            2: inj_selected_output_1755007782414_602 = data_ts1755007782414[2];
            3: inj_selected_output_1755007782414_602 = data_ts1755007782414[3];
            default: inj_selected_output_1755007782414_602 = 8'hXX;
        endcase
    end
    // END: generate_for_block_ts1755007782414

    multiplexer_2to1 multiplexer_2to1_inst_1755007782414_9856 (
        .result(inj_result_1755007782414_168),
        .data0(inj_data0_1755007782414_431),
        .data1(inj_data1_1755007782414_10),
        .sel(inj_sel_1755007782414_831)
    );
endmodule

