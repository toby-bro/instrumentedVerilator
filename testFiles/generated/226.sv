module MiscExpressions_ValueRange (
    input logic [15:0] in_vector,
    output logic [7:0] out_slice
);
    always_comb begin
        out_slice = in_vector[7:0];
    end
endmodule

module ansi_basic (
    input logic clk,
    output logic reset_n
);
    always_comb begin
        reset_n = clk;
    end
endmodule

module casez_xz (
    input logic [2:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            3'b1??: out_res = 1'b1;
            3'b0z?: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module child_concat_output (
    input logic dummy_in,
    output logic [7:0] data
);
    assign data = dummy_in ? 8'hAA : 8'h55;
endmodule

module nested_module (
    input logic nm_in,
    output logic nm_out
);
    assign nm_out = nm_in;
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_control_1755007829679_193,
    input logic [7:0] inj_data_a_1755007829679_771,
    input logic [7:0] inj_data_b_1755007829679_591,
    input wire [31:0] inj_data_in_1755007829696_475,
    input wire [3:0] inj_data_in_1755007829706_924,
    input logic inj_dummy_in_non_ansi_1755007829682_378,
    input bit [7:0] inj_in_cmd_1755007829700_699,
    input logic [1:0] inj_in_val_1755007829679_209,
    input logic [2:0] inj_in_val_1755007829710_483,
    input logic [15:0] inj_in_vector_1755007829715_983,
    input logic inj_nm_in_1755007829682_629,
    input wire reset,
    output logic [7:0] inj_data_1755007829704_16,
    output logic [7:0] inj_data_1755007829719_465,
    output wire inj_data_d_1755007829687_509,
    output logic [7:0] inj_data_out_1755007829694_29,
    output logic [31:0] inj_data_out_1755007829696_49,
    output reg [3:0] inj_data_out_1755007829706_18,
    output logic inj_dummy_out_non_ansi_1755007829682_124,
    output logic inj_fs_out_target_1755007829699_707,
    output logic inj_named_conn_out_1755007829682_721,
    output logic inj_nm_out_1755007829682_56,
    output logic [7:0] inj_out1_1755007829690_155,
    output logic [7:0] inj_out1_1755007829702_390,
    output logic [7:0] inj_out2_1755007829690_151,
    output logic [7:0] inj_out2_1755007829702_9,
    output logic [7:0] inj_out_1755007829681_801,
    output reg inj_out_res_1755007829679_380,
    output reg inj_out_res_1755007829684_298,
    output reg inj_out_res_1755007829710_144,
    output logic [7:0] inj_out_slice_1755007829715_229,
    output bit [3:0] inj_out_status_1755007829700_669,
    output logic [7:0] inj_out_sum_1755007829697_554,
    output logic [7:0] inj_out_x_j_1755007829685_294,
    output logic [7:0] inj_out_y_j_1755007829685_299,
    output logic inj_reset_n_1755007829689_400,
    output logic [7:0] inj_result1_1755007829679_471,
    output logic [7:0] inj_result2_1755007829679_720
);
    // BEGIN: case_empty_statement_ts1755007829679
    // BEGIN: dup_cond_ts1755007829680
    // BEGIN: simple_assign_ts1755007829681
    // BEGIN: explicit_non_ansi_ports_module_ts1755007829683
    input logic inj_nm_in_1755007829682_629_ts1755007829683;
    output logic inj_named_conn_out_1755007829682_721_ts1755007829683;
    input logic inj_dummy_in_non_ansi_1755007829682_378_ts1755007829683;
    output logic inj_dummy_out_non_ansi_1755007829682_124_ts1755007829683;
        // BEGIN: dup_expr_ts1755007829692
        logic [7:0] temp_add_ts1755007829692;
        logic [7:0] temp_mult_ts1755007829692;
        logic [7:0] inter1_ts1755007829692;
        logic [7:0] inter2_ts1755007829692;
        logic [7:0] complex_expr_ts1755007829692;
            // BEGIN: ModSampledVarLogic_ts1755007829694
            logic [7:0] __Vsampled_state = 8'hAB; 
            logic [7:0] internal_reg_ts1755007829694;
                // BEGIN: mod_part_select_ts1755007829696
                logic [31:0] temp_reg_ts1755007829696;
                    // BEGIN: simple_for_loop_ts1755007829697
                    logic [7:0] sum_ts1755007829697;
                        // BEGIN: child_concat_output_ts1755007829720
                        assign inj_data_1755007829719_465 = inj_nm_in_1755007829682_629_ts1755007829683 ? 8'hAA : 8'h55;
                        // END: child_concat_output_ts1755007829720

                        MiscExpressions_ValueRange MiscExpressions_ValueRange_inst_1755007829715_9537 (
                            .in_vector(inj_in_vector_1755007829715_983),
                            .out_slice(inj_out_slice_1755007829715_229)
                        );
                        casez_xz casez_xz_inst_1755007829710_926 (
                            .in_val(inj_in_val_1755007829710_483),
                            .out_res(inj_out_res_1755007829710_144)
                        );
                        // BEGIN: mod_event_implicit_ts1755007829706
                        always @* begin
                            inj_data_out_1755007829706_18 = inj_data_in_1755007829706_924;
                        end
                        // END: mod_event_implicit_ts1755007829706

                        child_concat_output child_concat_output_inst_1755007829704_9851 (
                            .dummy_in(inj_named_conn_out_1755007829682_721_ts1755007829683),
                            .data(inj_data_1755007829704_16)
                        );
                        // BEGIN: always_multi_stmt_unhandled_ts1755007829702
                        always_comb begin
                            inj_out1_1755007829702_390 = inj_data_a_1755007829679_771;
                            inj_out2_1755007829702_9 = sum_ts1755007829697;
                        end
                        // END: always_multi_stmt_unhandled_ts1755007829702

                        // BEGIN: mod_case_standard_ts1755007829700
                    always_comb begin
                        case (inj_in_cmd_1755007829700_699)
                            8'd0, 8'd1, 8'd2: begin
                                inj_out_status_1755007829700_669 = 4'hA;
                            end
                            8'd3, 8'd4: begin
                                inj_out_status_1755007829700_669 = 4'hB;
                            end
                            default: begin
                                inj_out_status_1755007829700_669 = 4'hF;
                            end
                        endcase
                    end
                        // END: mod_case_standard_ts1755007829700

                        // BEGIN: mod_fixup_target_ts1755007829699
                        assign inj_fs_out_target_1755007829699_707 = inj_dummy_in_non_ansi_1755007829682_378_ts1755007829683;
                        // END: mod_fixup_target_ts1755007829699

                    always_comb begin
                        sum_ts1755007829697 = 8'h00;
                        for (int i = 0; i < 5; i = i + 1) begin
                            sum_ts1755007829697 = sum_ts1755007829697 + internal_reg_ts1755007829694;
                        end
                        inj_out_sum_1755007829697_554 = sum_ts1755007829697;
                    end
                    // END: simple_for_loop_ts1755007829697

                always_comb begin
                    temp_reg_ts1755007829696[7:0] = inj_data_in_1755007829696_475[7:0];
                    temp_reg_ts1755007829696[15:8] = inj_data_in_1755007829696_475[23:16];
                    temp_reg_ts1755007829696[31:16] = inj_data_in_1755007829696_475[15:0];
                    temp_reg_ts1755007829696[0] = inj_data_in_1755007829696_475[31];
                    temp_reg_ts1755007829696[8] = inj_data_in_1755007829696_475[0];
                    inj_data_out_1755007829696_49 = temp_reg_ts1755007829696;
                end
                // END: mod_part_select_ts1755007829696

            always @(posedge clk) begin
            if (inj_control_1755007829679_193 == 4'd5) begin 
                internal_reg_ts1755007829694 <= __Vsampled_state + inj_control_1755007829679_193; 
            end else if (inj_control_1755007829679_193 > 4'd8) begin 
                internal_reg_ts1755007829694 <= {4'h0, inj_control_1755007829679_193} - 1; 
            end else begin
                internal_reg_ts1755007829694 <= 8'hFF;
            end
            end
            assign inj_data_out_1755007829694_29 = internal_reg_ts1755007829694;
            // END: ModSampledVarLogic_ts1755007829694

        always_comb begin
            temp_add_ts1755007829692 = inj_data_b_1755007829679_591 + inj_data_a_1755007829679_771;
            inj_out1_1755007829690_155 = temp_add_ts1755007829692;
            inj_out2_1755007829690_151 = inj_data_b_1755007829679_591 + inj_data_a_1755007829679_771;
            inter1_ts1755007829692 = inj_data_b_1755007829679_591 * 2;
            inter2_ts1755007829692 = inj_data_a_1755007829679_771 * 2;
            temp_mult_ts1755007829692 = inter1_ts1755007829692 + inter2_ts1755007829692;
            complex_expr_ts1755007829692 = (inj_data_b_1755007829679_591 + inj_data_a_1755007829679_771) * (inj_data_b_1755007829679_591 - inj_data_a_1755007829679_771) + (inj_data_b_1755007829679_591 + inj_data_a_1755007829679_771);
            if (inj_data_b_1755007829679_591 > inj_data_a_1755007829679_771) begin
                inj_out1_1755007829690_155 = temp_mult_ts1755007829692;
            end else begin
                inj_out1_1755007829690_155 = temp_add_ts1755007829692;
            end
            if (inj_data_a_1755007829679_771 >= inj_data_b_1755007829679_591) begin
                inj_out2_1755007829690_151 = temp_add_ts1755007829692;
            end else begin
                inj_out2_1755007829690_151 = temp_mult_ts1755007829692;
            end
            inj_out1_1755007829690_155 = inj_out1_1755007829690_155 + complex_expr_ts1755007829692;
        end
        // END: dup_expr_ts1755007829692

        ansi_basic ansi_basic_inst_1755007829689_2082 (
            .clk(clk),
            .reset_n(inj_reset_n_1755007829689_400)
        );
        // BEGIN: simple_logic_b_ts1755007829687
        assign inj_data_d_1755007829687_509 = clk;
        // END: simple_logic_b_ts1755007829687

        // BEGIN: split_multiple_in_branch_ts1755007829686
        always @(posedge clk) begin
            if (inj_nm_in_1755007829682_629_ts1755007829683) begin
                inj_out_x_j_1755007829685_294 <= inj_data_b_1755007829679_591 * 3;
                inj_out_y_j_1755007829685_299 <= inj_data_a_1755007829679_771 + 1;
            end else begin
                inj_out_x_j_1755007829685_294 <= inj_data_b_1755007829679_591;
                inj_out_y_j_1755007829685_299 <= inj_data_a_1755007829679_771;
            end
        end
        // END: split_multiple_in_branch_ts1755007829686

        // BEGIN: case_basic_ts1755007829684
        always_comb begin
            inj_out_res_1755007829684_298 = 1'b0;
            case (inj_in_val_1755007829679_209)
                2'b00: inj_out_res_1755007829684_298 = 1'b0;
                2'b01: inj_out_res_1755007829684_298 = 1'b1;
                2'b10: inj_out_res_1755007829684_298 = 1'b0;
                2'b11: inj_out_res_1755007829684_298 = 1'b1;
            endcase
        end
        // END: case_basic_ts1755007829684

    assign inj_named_conn_out_1755007829682_721_ts1755007829683 = inj_nm_in_1755007829682_629_ts1755007829683;
    assign inj_dummy_out_non_ansi_1755007829682_124_ts1755007829683 = inj_dummy_in_non_ansi_1755007829682_378_ts1755007829683;
    // END: explicit_non_ansi_ports_module_ts1755007829683

    nested_module nested_module_inst_1755007829682_476 (
        .nm_in(inj_nm_in_1755007829682_629),
        .nm_out(inj_nm_out_1755007829682_56)
    );
    assign inj_out_1755007829681_801 = inj_data_b_1755007829679_591;
    // END: simple_assign_ts1755007829681

    always_comb begin
        inj_result1_1755007829679_471 = '0;
        inj_result2_1755007829679_720 = '0;
        if (inj_control_1755007829679_193[0]) begin
            inj_result1_1755007829679_471 = inj_data_a_1755007829679_771 + inj_data_b_1755007829679_591;
        end else begin
            inj_result1_1755007829679_471 = inj_data_a_1755007829679_771 - inj_data_b_1755007829679_591;
        end
        if (inj_control_1755007829679_193[1]) begin
            inj_result2_1755007829679_720 = inj_data_a_1755007829679_771 - inj_data_b_1755007829679_591;
        end else begin
            inj_result2_1755007829679_720 = inj_data_a_1755007829679_771 + inj_data_b_1755007829679_591;
        end
        case (inj_control_1755007829679_193[3:2])
            2'b00: inj_result1_1755007829679_471 = inj_data_a_1755007829679_771 & inj_data_b_1755007829679_591;
            2'b01: inj_result1_1755007829679_471 = inj_data_a_1755007829679_771 | inj_data_b_1755007829679_591;
            2'b10: inj_result2_1755007829679_720 = inj_data_a_1755007829679_771 & inj_data_b_1755007829679_591;
            2'b11: inj_result2_1755007829679_720 = inj_data_a_1755007829679_771 | inj_data_b_1755007829679_591;
            default: begin inj_result1_1755007829679_471 = '0; inj_result2_1755007829679_720 = '0; end
        endcase
        if (inj_control_1755007829679_193[0] == inj_control_1755007829679_193[1]) begin
            inj_result1_1755007829679_471 = inj_result1_1755007829679_471 + 1;
        end else if (inj_control_1755007829679_193[2] != inj_control_1755007829679_193[3]) begin
            inj_result2_1755007829679_720 = inj_result2_1755007829679_720 - 1;
        end
    end
    // END: dup_cond_ts1755007829680

    always_comb begin
        inj_out_res_1755007829679_380 = 1'b0;
        case (inj_in_val_1755007829679_209)
            2'b00: inj_out_res_1755007829679_380 = 1'b1;
            2'b01: ;
            2'b10: inj_out_res_1755007829679_380 = 1'b0;
            default: inj_out_res_1755007829679_380 = 1'b1;
        endcase
    end
    // END: case_empty_statement_ts1755007829679
endmodule

