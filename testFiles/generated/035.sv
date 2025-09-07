module BitwiseAssign (
    input logic [3:0] in_a,
    input logic [3:0] in_b,
    output logic [3:0] out_y
);
    assign out_y = in_a ^ in_b;
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755007762369_501,
    input logic [3:0] inj_a_1755007762370_793,
    input logic inj_b_1755007762369_726,
    input logic [3:0] inj_b_1755007762370_948,
    input logic [7:0] inj_c_1755007762370_677,
    input int inj_config_data_in_1755007762378_228,
    input wire [1:0] inj_dtl_action_sel_1755007762370_641,
    input wire [7:0] inj_dtl_data_a_1755007762370_783,
    input wire [7:0] inj_dtl_data_b_1755007762370_141,
    input bit inj_enable_crypto_1755007762371_69,
    input wire reset,
    output int inj_config_data_out_1755007762378_363,
    output bit inj_crypto_active_1755007762371_526,
    output logic [7:0] inj_dtl_result_reg_1755007762370_884,
    output logic [15:0] inj_out_concat_1755007762370_634,
    output logic [3:0] inj_out_h_1755007762372_77,
    output logic [3:0] inj_out_l_1755007762372_866,
    output logic [7:0] inj_out_x_j_1755007762373_768,
    output logic [3:0] inj_out_y_1755007762370_821,
    output logic [7:0] inj_out_y_j_1755007762373_895,
    output logic inj_q_1755007762376_16,
    output logic inj_sum_1755007762369_452
);
    // BEGIN: simple_adder_ts1755007762369
    // BEGIN: ConcatVectorOps_ts1755007762370
    // BEGIN: deep_task_logic_ts1755007762371
    task automatic perform_action;
        input [7:0] in_a;
        input [7:0] in_b;
        input [1:0] action;
        output logic [7:0] calculated_res_ts1755007762370;
        logic [7:0] temp_task_calc_ts1755007762370;
        if (action[0]) begin
            if (action[1]) begin
                temp_task_calc_ts1755007762370 = in_a + in_b;
            end else begin
                temp_task_calc_ts1755007762370 = in_a - in_b;
            end
        end else begin
            if (action[1]) begin
                temp_task_calc_ts1755007762370 = in_a & in_b;
            end else begin
                temp_task_calc_ts1755007762370 = in_a | in_b;
            end
        end
        case (temp_task_calc_ts1755007762370[1:0])
            2'b00: calculated_res_ts1755007762370 = temp_task_calc_ts1755007762370 ^ 8'hFF;
            2'b01: calculated_res_ts1755007762370 = temp_task_calc_ts1755007762370 + 1;
            2'b10: calculated_res_ts1755007762370 = temp_task_calc_ts1755007762370 - 1;
            default: calculated_res_ts1755007762370 = temp_task_calc_ts1755007762370;
        endcase
    endtask
    always_ff @(posedge clk or negedge reset) begin
        if (!reset) begin
            inj_dtl_result_reg_1755007762370_884 <= 8'd0;
        end else begin
            logic [7:0] next_dtl_result_ts1755007762370;
                // BEGIN: PragmaProtectOptions_ts1755007762378
            `ifdef SLANG_PRAGMA
            `protect encoding (enctype="base64", line_length=76, bytes=1024)
            `endif
            `ifdef SLANG_PRAGMA
            `protect license (library="my_project_lib", entry="start_feature_A", match=42, feature="feature_set_B", exit="end_feature_A")
            `endif
            `ifdef SLANG_PRAGMA
            `protect reset
            `endif
            `ifdef SLANG_PRAGMA
            `protect viewport (object="design.module_a.instance_b.register_c", access="read-only")
            `endif
            assign inj_config_data_out_1755007762378_363 = inj_config_data_in_1755007762378_228 + 1;
                // END: PragmaProtectOptions_ts1755007762378

                // BEGIN: mod_seq_reg_ts1755007762376
                always_ff @(posedge clk) begin
                    inj_q_1755007762376_16 <= inj_b_1755007762369_726;
                end
                // END: mod_seq_reg_ts1755007762376

                // BEGIN: split_multiple_in_branch_ts1755007762374
                always @(posedge clk) begin
                    if (inj_b_1755007762369_726) begin
                        inj_out_x_j_1755007762373_768 <= inj_c_1755007762370_677 * 3;
                        inj_out_y_j_1755007762373_895 <= next_dtl_result_ts1755007762370 + 1;
                    end else begin
                        inj_out_x_j_1755007762373_768 <= inj_c_1755007762370_677;
                        inj_out_y_j_1755007762373_895 <= next_dtl_result_ts1755007762370;
                    end
                end
                // END: split_multiple_in_branch_ts1755007762374

                // BEGIN: concat_assign_ts1755007762372
                assign {inj_out_h_1755007762372_77, inj_out_l_1755007762372_866} = next_dtl_result_ts1755007762370;
                // END: concat_assign_ts1755007762372

                // BEGIN: PragmaProtectKeyBlock_ts1755007762371
            `ifdef SLANG_PRAGMA
            `protect key
            `endif
            `ifdef SLANG_PRAGMA
            `protect block
            `endif
            assign inj_crypto_active_1755007762371_526 = inj_enable_crypto_1755007762371_69;
                // END: PragmaProtectKeyBlock_ts1755007762371

            if (reset) begin
                perform_action(inj_dtl_data_a_1755007762370_783, inj_dtl_data_b_1755007762370_141, inj_dtl_action_sel_1755007762370_641, next_dtl_result_ts1755007762370);
            end else begin
                next_dtl_result_ts1755007762370 = inj_dtl_result_reg_1755007762370_884;
            end
            inj_dtl_result_reg_1755007762370_884 <= next_dtl_result_ts1755007762370;
        end
    end
    // END: deep_task_logic_ts1755007762371

    BitwiseAssign BitwiseAssign_inst_1755007762370_1316 (
        .in_a(inj_a_1755007762370_793),
        .in_b(inj_b_1755007762370_948),
        .out_y(inj_out_y_1755007762370_821)
    );
    assign inj_out_concat_1755007762370_634 = {inj_a_1755007762370_793, inj_b_1755007762370_948, inj_c_1755007762370_677};
    // END: ConcatVectorOps_ts1755007762370

    assign inj_sum_1755007762369_452 = inj_a_1755007762369_501 + inj_b_1755007762369_726;
    // END: simple_adder_ts1755007762369
endmodule

