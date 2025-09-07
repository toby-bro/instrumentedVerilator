module Module_ConfigKeywords (
    input bit cfg_in,
    output bit cfg_out
);
    assign cfg_out = cfg_in;
endmodule

module unreferenced_module (
    input logic unused_in,
    output logic unused_out
);
    assign unused_out = ~unused_in;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_arg_in_task_1755007901577_408,
    input bit inj_cfg_in_1755007901577_774,
    input logic [7:0] inj_data_a_init_task_1755007901577_430,
    input logic [15:0] inj_data_in_pa_1755007901580_597,
    input wire [1:0] inj_dtl_action_sel_1755007901582_495,
    input wire [7:0] inj_dtl_data_a_1755007901582_580,
    input wire [7:0] inj_dtl_data_b_1755007901582_808,
    input logic inj_in_k_1755007901586_536,
    input logic inj_unused_in_1755007901577_140,
    input wire reset,
    output bit inj_cfg_out_1755007901577_291,
    output logic [7:0] inj_data_a_out_task_1755007901577_338,
    output logic [7:0] inj_data_b_out_task_1755007901577_704,
    output logic [7:0] inj_data_out_pa_1755007901580_502,
    output logic [3:0] inj_data_out_pv_1755007901580_724,
    output logic [7:0] inj_dtl_result_reg_1755007901582_274,
    output logic inj_o_out_1755007901579_473,
    output logic inj_out_l_1755007901586_60,
    output logic inj_unused_out_1755007901577_830
);
    // BEGIN: module_task_args_ts1755007901578
    logic [7:0] data_a_ts1755007901578 ;
    logic [7:0] data_b_ts1755007901578 ;
        // BEGIN: module_packed_variables_ts1755007901580
        logic [31:0] data_pv_ts1755007901580 ;
            // BEGIN: deep_task_logic_ts1755007901583
            task automatic perform_action;
                input [7:0] in_a;
                input [7:0] in_b;
                input [1:0] action;
                output logic [7:0] calculated_res_ts1755007901583;
                logic [7:0] temp_task_calc_ts1755007901583;
                if (action[0]) begin
                    if (action[1]) begin
                        temp_task_calc_ts1755007901583 = in_a + in_b;
                    end else begin
                        temp_task_calc_ts1755007901583 = in_a - in_b;
                    end
                end else begin
                    if (action[1]) begin
                        temp_task_calc_ts1755007901583 = in_a & in_b;
                    end else begin
                        temp_task_calc_ts1755007901583 = in_a | in_b;
                    end
                end
                case (temp_task_calc_ts1755007901583[1:0])
                    2'b00: calculated_res_ts1755007901583 = temp_task_calc_ts1755007901583 ^ 8'hFF;
                    2'b01: calculated_res_ts1755007901583 = temp_task_calc_ts1755007901583 + 1;
                    2'b10: calculated_res_ts1755007901583 = temp_task_calc_ts1755007901583 - 1;
                    default: calculated_res_ts1755007901583 = temp_task_calc_ts1755007901583;
                endcase
            endtask
            always_ff @(posedge clk or negedge reset) begin
                if (!reset) begin
                    inj_dtl_result_reg_1755007901582_274 <= 8'd0;
                end else begin
                    logic [7:0] next_dtl_result_ts1755007901583;
                        // BEGIN: LintLatch_ts1755007901586
                        always_comb begin
                            if (inj_unused_in_1755007901577_140) begin
                                inj_out_l_1755007901586_60 = inj_in_k_1755007901586_536;
                            end else begin
                                inj_out_l_1755007901586_60 = 1'b0; 
                            end
                        end
                        // END: LintLatch_ts1755007901586

                    if (reset) begin
                        perform_action(inj_dtl_data_a_1755007901582_580, inj_dtl_data_b_1755007901582_808, inj_dtl_action_sel_1755007901582_495, next_dtl_result_ts1755007901583);
                    end else begin
                        next_dtl_result_ts1755007901583 = inj_dtl_result_reg_1755007901582_274;
                    end
                    inj_dtl_result_reg_1755007901582_274 <= next_dtl_result_ts1755007901583;
                end
            end
            // END: deep_task_logic_ts1755007901583

        logic [7:0] data_pa[0:1] ;
        always_comb begin
            if (inj_unused_in_1755007901577_140) begin
                data_pv_ts1755007901580[7:0] = data_b_ts1755007901578;
                data_pv_ts1755007901580[15:8] = ~data_b_ts1755007901578;
                data_pv_ts1755007901580[23:16] = data_pv_ts1755007901580[7:0];
                data_pv_ts1755007901580[31:24] = data_pv_ts1755007901580[15:8];
                data_pa[0] = inj_data_in_pa_1755007901580_597[7:0];
                data_pa[1] = inj_data_in_pa_1755007901580_597[15:8];
            end else begin
                data_pv_ts1755007901580 = 32'h0;
                data_pa[0] = 8'h0;
                data_pa[1] = 8'h0;
            end
        end
        assign inj_data_out_pv_1755007901580_724 = data_pv_ts1755007901580[3:0];
        assign inj_data_out_pa_1755007901580_502 = data_pa[0];
        // END: module_packed_variables_ts1755007901580

        // BEGIN: extern_declarations_ts1755007901579
        assign inj_o_out_1755007901579_473 = inj_unused_in_1755007901577_140;
        // END: extern_declarations_ts1755007901579

    task automatic modify_vars;
        input logic [7:0] task_arg_ts1755007901578;
        logic [7:0] task_local_ts1755007901578 ;
        begin
            task_local_ts1755007901578 = task_arg_ts1755007901578;
            data_a_ts1755007901578 = task_local_ts1755007901578 + 8'd1;
            data_b_ts1755007901578 = task_arg_ts1755007901578 - 8'd1;
        end
    endtask
    always_comb begin
        if (inj_unused_in_1755007901577_140) begin
            data_a_ts1755007901578 = inj_data_a_init_task_1755007901577_430;
            data_b_ts1755007901578 = 8'hFF;
            modify_vars(inj_arg_in_task_1755007901577_408);
        end else begin
            data_a_ts1755007901578 = 8'h00;
            data_b_ts1755007901578 = 8'h00;
        end
    end
    always_comb begin
        inj_data_a_out_task_1755007901577_338 = data_a_ts1755007901578 + 8'd2;
        inj_data_b_out_task_1755007901577_704 = data_b_ts1755007901578;
    end
    // END: module_task_args_ts1755007901578

    unreferenced_module unreferenced_module_inst_1755007901577_1631 (
        .unused_in(inj_unused_in_1755007901577_140),
        .unused_out(inj_unused_out_1755007901577_830)
    );
    Module_ConfigKeywords Module_ConfigKeywords_inst_1755007901577_7656 (
        .cfg_in(inj_cfg_in_1755007901577_774),
        .cfg_out(inj_cfg_out_1755007901577_291)
    );
endmodule

