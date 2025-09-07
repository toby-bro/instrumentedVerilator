interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module LintImplicitWidth (
    input logic [7:0] in_wide,
    output logic [3:0] out_narrow
);
    assign out_narrow = in_wide;
endmodule

module LintParamUnused #(
    parameter integer UNUSED_PARAM = 8
) (
    input logic in_m,
    output logic out_n
);
    assign out_n = in_m;
endmodule

module ModSampledVarLogic (
    input logic clk,
    input logic [3:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] __Vsampled_state = 8'hAB; 
    logic [7:0] internal_reg;
    always @(posedge clk) begin
    if (data_in == 4'd5) begin 
        internal_reg <= __Vsampled_state + data_in; 
    end else if (data_in > 4'd8) begin 
        internal_reg <= {4'h0, data_in} - 1; 
    end else begin
        internal_reg <= 8'hFF;
    end
    end
    assign data_out = internal_reg;
endmodule

module generate_for_block (
    input logic [1:0] selector,
    output logic [7:0] selected_output
);
    wire [7:0] data [3:0]; 
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : data_gen
            assign data[i] = 8'(i + 1) * 8'(i + 1);
        end
    endgenerate
    always_comb begin
        case (selector)
            0: selected_output = data[0];
            1: selected_output = data[1];
            2: selected_output = data[2];
            3: selected_output = data[3];
            default: selected_output = 8'hXX;
        endcase
    end
endmodule

module mod_if_else_simple (
    input bit [3:0] in_data,
    output bit [3:0] out_result
);
always_comb begin
    if (in_data > 8) begin
        out_result = in_data + 1;
    end else begin
        out_result = in_data - 1;
    end
end
endmodule

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module split_arith_nb (
    input logic clk_v,
    input logic [7:0] op1_v,
    input logic [7:0] op2_v,
    output logic [7:0] diff_v,
    output logic [7:0] prod_v,
    output logic [7:0] sum_v
);
    always @(posedge clk_v) begin
        sum_v <= op1_v + op2_v;
        diff_v <= op1_v - op2_v;
        prod_v <= op1_v * op2_v;
    end
endmodule

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module snippet #(
    parameter int WIDTH = 8
) (
    input wire clk,
    input logic inj_comb_in2_1755007820147_979,
    input logic [3:0] inj_data_in_1755007820127_632,
    input logic [31:0] inj_data_in_w_1755007820134_969,
    input wire [1:0] inj_dtl_action_sel_1755007820130_845,
    input wire [7:0] inj_dtl_data_a_1755007820130_83,
    input wire [7:0] inj_dtl_data_b_1755007820130_664,
    input int inj_i_val_1755007820181_418,
    input bit inj_in_bit_1755007820162_904,
    input bit [3:0] inj_in_data_1755007820139_305,
    input integer inj_in_int_1755007820150_131,
    input logic [15:0] inj_in_u16_1755007820150_613,
    input logic [7:0] inj_op1_v_1755007820127_393,
    input logic [7:0] inj_op2_v_1755007820127_0,
    input logic [1:0] inj_selector_1755007820127_443,
    input logic inj_seq_in_1755007820147_856,
    input logic inj_task_en_1755007820129_45,
    input wire reset,
    output logic inj_comb_out_1755007820147_175,
    output logic [7:0] inj_data_out_1755007820127_67,
    output logic inj_data_out_1755007820170_123,
    output logic [7:0] inj_data_out_k_1755007820155_552,
    output logic [31:0] inj_data_out_w_1755007820134_426,
    output logic [7:0] inj_diff_v_1755007820127_465,
    output logic [7:0] inj_dtl_result_reg_1755007820130_925,
    output logic inj_is_even_1755007820144_949,
    output logic [7:0] inj_o_out_1755007820167_325,
    output logic inj_o_p_and_1755007820178_842,
    output logic inj_o_p_xor_1755007820178_846,
    output logic [7:0] inj_o_result_1755007820136_469,
    output logic inj_o_status_1755007820136_555,
    output int inj_o_val_1755007820181_578,
    output logic inj_out_logic_1755007820162_463,
    output logic inj_out_n_1755007820159_643,
    output logic [3:0] inj_out_narrow_1755007820141_624,
    output reg inj_out_res_1755007820128_733,
    output bit [3:0] inj_out_result_1755007820139_459,
    output logic signed [15:0] inj_out_s16_1755007820150_958,
    output logic signed [31:0] inj_out_s32_from_int_1755007820150_537,
    output logic signed [31:0] inj_out_s32_from_l32_1755007820150_880,
    output logic [31:0] inj_out_u32_from_int_1755007820150_379,
    output logic [31:0] inj_out_u32_from_l32_1755007820150_479,
    output logic [7:0] inj_out_u8_1755007820150_613,
    output logic [7:0] inj_prod_v_1755007820127_120,
    output logic inj_q_1755007820173_839,
    output logic [7:0] inj_result_m_1755007820175_461,
    output logic [7:0] inj_selected_output_1755007820127_428,
    output logic inj_seq_out_1755007820147_718,
    output logic [7:0] inj_sum_v_1755007820127_483,
    output logic inj_task_output_valid_1755007820129_472
);
    // BEGIN: case_default_ts1755007820128
    // BEGIN: module_task_write_ts1755007820130
    // BEGIN: deep_task_logic_ts1755007820132
    task automatic perform_action;
        input [7:0] in_a;
        input [7:0] in_b;
        input [1:0] action;
        output logic [7:0] calculated_res_ts1755007820132;
        logic [7:0] temp_task_calc_ts1755007820132;
        if (action[0]) begin
            if (action[1]) begin
                temp_task_calc_ts1755007820132 = in_a + in_b;
            end else begin
                temp_task_calc_ts1755007820132 = in_a - in_b;
            end
        end else begin
            if (action[1]) begin
                temp_task_calc_ts1755007820132 = in_a & in_b;
            end else begin
                temp_task_calc_ts1755007820132 = in_a | in_b;
            end
        end
        case (temp_task_calc_ts1755007820132[1:0])
            2'b00: calculated_res_ts1755007820132 = temp_task_calc_ts1755007820132 ^ 8'hFF;
            2'b01: calculated_res_ts1755007820132 = temp_task_calc_ts1755007820132 + 1;
            2'b10: calculated_res_ts1755007820132 = temp_task_calc_ts1755007820132 - 1;
            default: calculated_res_ts1755007820132 = temp_task_calc_ts1755007820132;
        endcase
    endtask
    always_ff @(posedge clk or negedge reset) begin
        if (!reset) begin
            inj_dtl_result_reg_1755007820130_925 <= 8'd0;
        end else begin
            logic [7:0] next_dtl_result_ts1755007820132;
                // BEGIN: MixedLogic_ts1755007820147
                logic seq_reg_ts1755007820147;
                logic comb_intermediate_ts1755007820147;
                    // BEGIN: mod_module_attrs_ts1755007820168
                    logic [WIDTH-1:0] r_data_ts1755007820168;
                        // BEGIN: ModClockedConditional_ts1755007820170
                        logic reg_data_ts1755007820170;
                            // BEGIN: mod_automatic_task_ts1755007820181
                            task automatic update_val(input int in_v, output int out_v);
                                out_v = in_v * 2;
                            endtask
                            always_comb begin
                                int temp_val_ts1755007820181;
                                update_val(inj_i_val_1755007820181_418, temp_val_ts1755007820181);
                                inj_o_val_1755007820181_578 = temp_val_ts1755007820181;
                            end
                            // END: mod_automatic_task_ts1755007820181

                            // BEGIN: primitive_example_ts1755007820178
                            and (inj_o_p_and_1755007820178_842, reg_data_ts1755007820170, inj_task_en_1755007820129_45);
                            xor (inj_o_p_xor_1755007820178_846, reg_data_ts1755007820170, inj_task_en_1755007820129_45);
                            // END: primitive_example_ts1755007820178

                            // BEGIN: split_nested_if_ts1755007820175
                            always @(posedge clk) begin
                                if (comb_intermediate_ts1755007820147) begin
                                    if (inj_task_en_1755007820129_45) begin
                                        inj_result_m_1755007820175_461 <= inj_op2_v_1755007820127_0;
                                    end else begin
                                        inj_result_m_1755007820175_461 <= next_dtl_result_ts1755007820132;
                                    end
                                end else begin
                                    inj_result_m_1755007820175_461 <= inj_op1_v_1755007820127_393;
                                end
                            end
                            // END: split_nested_if_ts1755007820175

                            // BEGIN: basic_d_flipflop_ts1755007820173
                            always_ff @(posedge clk) begin
                                inj_q_1755007820173_839 <= seq_reg_ts1755007820147;
                            end
                            // END: basic_d_flipflop_ts1755007820173

                        always @(posedge clk) begin
                        if (inj_comb_in2_1755007820147_979) begin
                            reg_data_ts1755007820170 <= seq_reg_ts1755007820147;
                        end
                        end
                        assign inj_data_out_1755007820170_123 = reg_data_ts1755007820170;
                        // END: ModClockedConditional_ts1755007820170

                    always_comb begin
                        r_data_ts1755007820168 = inj_dtl_data_a_1755007820130_83;
                    end
                    assign inj_o_out_1755007820167_325 = r_data_ts1755007820168;
                    // END: mod_module_attrs_ts1755007820168

                    // BEGIN: DummyHierModule_ts1755007820162
                    assign inj_out_logic_1755007820162_463 = inj_in_bit_1755007820162_904;
                    // END: DummyHierModule_ts1755007820162

                    LintParamUnused LintParamUnused_inst_1755007820159_4053 (
                        .in_m(comb_intermediate_ts1755007820147),
                        .out_n(inj_out_n_1755007820159_643)
                    );
                    // BEGIN: split_input_only_var_ts1755007820155
                    always @(posedge clk) begin
                        if (inj_comb_in2_1755007820147_979) begin
                            inj_data_out_k_1755007820155_552 <= next_dtl_result_ts1755007820132;
                        end
                    end
                    // END: split_input_only_var_ts1755007820155

                    // BEGIN: SignedUnsignedConversions_ts1755007820151
                    always_comb begin
                        inj_out_u8_1755007820150_613 = $unsigned(inj_op1_v_1755007820127_393);
                        inj_out_s16_1755007820150_958 = $signed(inj_in_u16_1755007820150_613);
                        inj_out_s32_from_l32_1755007820150_880 = $signed(inj_data_in_w_1755007820134_969);
                        inj_out_u32_from_l32_1755007820150_479 = $unsigned(inj_data_in_w_1755007820134_969);
                        inj_out_s32_from_int_1755007820150_537 = $signed(inj_in_int_1755007820150_131);
                        inj_out_u32_from_int_1755007820150_379 = $unsigned(inj_in_int_1755007820150_131);
                    end
                    // END: SignedUnsignedConversions_ts1755007820151

                always @(posedge clk or negedge reset) begin
                    if (!reset) begin
                        seq_reg_ts1755007820147 <= 1'b0;
                    end else begin
                        seq_reg_ts1755007820147 <= inj_seq_in_1755007820147_856;
                    end
                end
                assign inj_seq_out_1755007820147_718 = seq_reg_ts1755007820147;
                always @(seq_reg_ts1755007820147 or inj_task_en_1755007820129_45 or inj_comb_in2_1755007820147_979) begin
                    comb_intermediate_ts1755007820147 = (seq_reg_ts1755007820147 & inj_task_en_1755007820129_45) | (~seq_reg_ts1755007820147 & inj_comb_in2_1755007820147_979);
                end
                assign inj_comb_out_1755007820147_175 = comb_intermediate_ts1755007820147;
                // END: MixedLogic_ts1755007820147

                // BEGIN: FunctionTaskMod_ts1755007820144
                function automatic bit check_even(input logic [7:0] v);
                    check_even = ~v[0];
                endfunction
                task automatic dummy_task(input logic [7:0] v);
                    int tmp_ts1755007820144;
                    tmp_ts1755007820144 = v;
                endtask
                assign inj_is_even_1755007820144_949 = check_even(inj_op1_v_1755007820127_393);
                // END: FunctionTaskMod_ts1755007820144

                LintImplicitWidth LintImplicitWidth_inst_1755007820141_2683 (
                    .out_narrow(inj_out_narrow_1755007820141_624),
                    .in_wide(inj_op2_v_1755007820127_0)
                );
                mod_if_else_simple mod_if_else_simple_inst_1755007820139_4016 (
                    .in_data(inj_in_data_1755007820139_305),
                    .out_result(inj_out_result_1755007820139_459)
                );
                // BEGIN: bind_directive_top_ts1755007820136
                target_module_for_bind target_inst(
                    .i_target_clk   (clk),
                    .i_target_data  (next_dtl_result_ts1755007820132),
                    .o_target_result(inj_o_result_1755007820136_469)
                );
                module_to_bind bind_inst(
                    .i_bind_clk     (clk),
                    .i_bind_control (inj_data_in_1755007820127_632),
                    .o_bind_status  (inj_o_status_1755007820136_555)
                );
                // END: bind_directive_top_ts1755007820136

                // BEGIN: ModWideBus_ts1755007820134
                assign inj_data_out_w_1755007820134_426 = ~inj_data_in_w_1755007820134_969;
                // END: ModWideBus_ts1755007820134

            if (reset) begin
                perform_action(inj_dtl_data_a_1755007820130_83, inj_dtl_data_b_1755007820130_664, inj_dtl_action_sel_1755007820130_845, next_dtl_result_ts1755007820132);
            end else begin
                next_dtl_result_ts1755007820132 = inj_dtl_result_reg_1755007820130_925;
            end
            inj_dtl_result_reg_1755007820130_925 <= next_dtl_result_ts1755007820132;
        end
    end
    // END: deep_task_logic_ts1755007820132

    my_if task_vif_inst();
    task automatic update_vif_signals(input logic en, input logic [7:0] data_val,
        output logic [7:0] vif_data, output logic vif_valid, output logic vif_ready);
        if (en) begin
            vif_data = data_val;
            vif_valid = 1'b1;
            vif_ready = 1'b0;
        end else begin
            vif_data = 8'h0;
            vif_valid = 1'b0;
            vif_ready = 1'b1;
        end
    endtask
    always_comb begin
        update_vif_signals(inj_task_en_1755007820129_45, inj_op1_v_1755007820127_393, task_vif_inst.data, task_vif_inst.valid, task_vif_inst.ready);
        inj_task_output_valid_1755007820129_472 = task_vif_inst.valid;
    end
    // END: module_task_write_ts1755007820130

    always_comb begin
        inj_out_res_1755007820128_733 = 1'b0;
        case (inj_selector_1755007820127_443)
            2'b01: inj_out_res_1755007820128_733 = 1'b1;
            2'b10: inj_out_res_1755007820128_733 = 1'b0;
            default: inj_out_res_1755007820128_733 = 1'b1;
        endcase
    end
    // END: case_default_ts1755007820128

    ModSampledVarLogic ModSampledVarLogic_inst_1755007820127_8256 (
        .clk(clk),
        .data_in(inj_data_in_1755007820127_632),
        .data_out(inj_data_out_1755007820127_67)
    );
    split_arith_nb split_arith_nb_inst_1755007820127_9468 (
        .prod_v(inj_prod_v_1755007820127_120),
        .sum_v(inj_sum_v_1755007820127_483),
        .clk_v(clk),
        .op1_v(inj_op1_v_1755007820127_393),
        .op2_v(inj_op2_v_1755007820127_0),
        .diff_v(inj_diff_v_1755007820127_465)
    );
    generate_for_block generate_for_block_inst_1755007820127_9674 (
        .selected_output(inj_selected_output_1755007820127_428),
        .selector(inj_selector_1755007820127_443)
    );
endmodule

