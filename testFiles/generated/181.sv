module loop_with_internal_assign (
    input logic [3:0] start_val,
    output logic [7:0] final_val
);
    logic [7:0] current_val;
    always_comb begin
        current_val = start_val;
        for (int k = 0; k < 3; k = k + 1) begin
            current_val = current_val + 1;
        end
        final_val = current_val;
    end
endmodule

module module_task_args (
    input logic [7:0] arg_in_task,
    input logic [7:0] data_a_init_task,
    input logic start_task,
    output logic [7:0] data_a_out_task,
    output logic [7:0] data_b_out_task
);
    logic [7:0] data_a ;
    logic [7:0] data_b ;
    task automatic modify_vars;
        input logic [7:0] task_arg;
        logic [7:0] task_local ;
        begin
            task_local = task_arg;
            data_a = task_local + 8'd1;
            data_b = task_arg - 8'd1;
        end
    endtask
    always_comb begin
        if (start_task) begin
            data_a = data_a_init_task;
            data_b = 8'hFF;
            modify_vars(arg_in_task);
        end else begin
            data_a = 8'h00;
            data_b = 8'h00;
        end
    end
    always_comb begin
        data_a_out_task = data_a + 8'd2;
        data_b_out_task = data_b;
    end
endmodule

module nets_alias_clocking (
    input logic i_clk,
    input logic i_data_sync,
    input logic i_reg_data,
    input wire i_wire_data,
    output logic o_reg_out,
    output wire o_wire_out
);
    wire  w_internal;
    logic r_internal;
    assign w_internal  = i_wire_data & i_reg_data;
    assign o_wire_out  = w_internal;
    always_ff @(posedge i_clk) r_internal <= i_data_sync;
    assign o_reg_out = r_internal;
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_data0_1755007813827_127,
    input logic [7:0] inj_data1_1755007813827_8,
    input logic [7:0] inj_data2_1755007813827_16,
    input logic [7:0] inj_data3_1755007813827_372,
    input logic [3:0] inj_flags_1755007813828_849,
    input logic inj_in_1755007813827_673,
    input integer inj_in_int_1755007813843_114,
    input logic [31:0] inj_in_l32_1755007813843_48,
    input logic [15:0] inj_in_u16_1755007813843_378,
    input logic [1:0] inj_sel_code_1755007813827_607,
    input wire reset,
    output logic [7:0] inj_data_a_out_task_1755007813833_958,
    output logic [7:0] inj_data_b_out_task_1755007813833_674,
    output logic [7:0] inj_final_val_1755007813839_187,
    output logic inj_named_out_1755007813827_803,
    output logic inj_o_reg_out_1755007813828_651,
    output logic inj_o_result_1755007813835_454,
    output wire inj_o_wire_out_1755007813828_537,
    output logic [7:0] inj_out1_1755007813828_735,
    output logic inj_out_i_1755007813831_375,
    output logic signed [15:0] inj_out_s16_1755007813843_960,
    output logic signed [31:0] inj_out_s32_from_int_1755007813843_865,
    output logic signed [31:0] inj_out_s32_from_l32_1755007813843_194,
    output logic [31:0] inj_out_u32_from_int_1755007813843_629,
    output logic [31:0] inj_out_u32_from_l32_1755007813843_804,
    output logic [7:0] inj_out_u8_1755007813843_148,
    output logic [7:0] inj_selected_data_1755007813827_530,
    output logic inj_sum_1755007813841_528,
    output logic [15:0] inj_sum_out_i_1755007813837_749
);
    // BEGIN: IfElseIfChain_ts1755007813827
    // BEGIN: module_with_param_ts1755007813827
    parameter int DELAY = 10;
    logic bind_dummy_in_ts1755007813827;
    logic bind_dummy_out_ts1755007813827;
        // BEGIN: dup_logic_ops_ts1755007813830
        logic cond1_ts1755007813829, cond2_ts1755007813829, cond3_ts1755007813829;
        logic complex_cond1_ts1755007813829, complex_cond2_ts1755007813829;
            // BEGIN: mod_simple_ref_ts1755007813835
            logic internal_sig_ts1755007813835;
                // BEGIN: SignedUnsignedConversions_ts1755007813844
                always_comb begin
                    inj_out_u8_1755007813843_148 = $unsigned(inj_data2_1755007813827_16);
                    inj_out_s16_1755007813843_960 = $signed(inj_in_u16_1755007813843_378);
                    inj_out_s32_from_l32_1755007813843_194 = $signed(inj_in_l32_1755007813843_48);
                    inj_out_u32_from_l32_1755007813843_804 = $unsigned(inj_in_l32_1755007813843_48);
                    inj_out_s32_from_int_1755007813843_865 = $signed(inj_in_int_1755007813843_114);
                    inj_out_u32_from_int_1755007813843_629 = $unsigned(inj_in_int_1755007813843_114);
                end
                // END: SignedUnsignedConversions_ts1755007813844

                simple_adder simple_adder_inst_1755007813841_8632 (
                    .a(bind_dummy_in_ts1755007813827),
                    .b(cond3_ts1755007813829),
                    .sum(inj_sum_1755007813841_528)
                );
                loop_with_internal_assign loop_with_internal_assign_inst_1755007813839_7428 (
                    .final_val(inj_final_val_1755007813839_187),
                    .start_val(inj_flags_1755007813828_849)
                );
                // BEGIN: split_for_loop_ts1755007813837
                always @(posedge clk) begin
                    inj_sum_out_i_1755007813837_749 <= 0;
                    for (int i = 0; i < 4; i = i + 1) begin
                        inj_sum_out_i_1755007813837_749 <= inj_sum_out_i_1755007813837_749 + inj_data3_1755007813827_372 + i;
                    end
                end
                // END: split_for_loop_ts1755007813837

            always_comb begin
                internal_sig_ts1755007813835 = inj_in_1755007813827_673;
                inj_o_result_1755007813835_454 = internal_sig_ts1755007813835;
            end
            // END: mod_simple_ref_ts1755007813835

            module_task_args module_task_args_inst_1755007813833_6343 (
                .start_task(inj_in_1755007813827_673),
                .data_a_out_task(inj_data_a_out_task_1755007813833_958),
                .data_b_out_task(inj_data_b_out_task_1755007813833_674),
                .arg_in_task(inj_data0_1755007813827_127),
                .data_a_init_task(inj_data2_1755007813827_16)
            );
            // BEGIN: LintAsyncFovIssue_ts1755007813831
            always_ff @(posedge clk or negedge reset) begin
                if (!reset) begin
                    inj_out_i_1755007813831_375 <= 1'b0;
                end else begin
                    inj_out_i_1755007813831_375 <= cond2_ts1755007813829 & inj_out_i_1755007813831_375;
                end
            end
            // END: LintAsyncFovIssue_ts1755007813831

        assign cond1_ts1755007813829 = inj_flags_1755007813828_849[0] && inj_flags_1755007813828_849[1];
        assign cond2_ts1755007813829 = inj_flags_1755007813828_849[2] || inj_flags_1755007813828_849[3];
        assign cond3_ts1755007813829 = !inj_flags_1755007813828_849[0];
        assign complex_cond1_ts1755007813829 = (cond1_ts1755007813829 || cond2_ts1755007813829) && cond3_ts1755007813829;
        assign complex_cond2_ts1755007813829 = !(inj_flags_1755007813828_849[0] && inj_flags_1755007813828_849[1]) || (inj_flags_1755007813828_849[2] || !inj_flags_1755007813828_849[3]);
        always_comb begin
            inj_out1_1755007813828_735 = '0;
            if (complex_cond1_ts1755007813829) begin
                inj_out1_1755007813828_735 = inj_data3_1755007813827_372 + inj_data2_1755007813827_16;
            end else begin
                inj_out1_1755007813828_735 = inj_data3_1755007813827_372 ^ inj_data0_1755007813827_127;
            end
            if (complex_cond2_ts1755007813829) begin
                inj_out1_1755007813828_735 = inj_out1_1755007813828_735 + inj_data0_1755007813827_127;
            end else begin
                inj_out1_1755007813828_735 = inj_out1_1755007813828_735 - inj_data0_1755007813827_127;
            end
            if ((inj_flags_1755007813828_849[0] && inj_flags_1755007813828_849[1]) && (!inj_flags_1755007813828_849[2] || inj_flags_1755007813828_849[3])) begin
                inj_out1_1755007813828_735 = inj_out1_1755007813828_735 * 2;
            end
        end
        // END: dup_logic_ops_ts1755007813830

        nets_alias_clocking nets_alias_clocking_inst_1755007813828_7505 (
            .i_clk(clk),
            .i_data_sync(bind_dummy_in_ts1755007813827),
            .i_reg_data(inj_in_1755007813827_673),
            .i_wire_data(reset),
            .o_reg_out(inj_o_reg_out_1755007813828_651),
            .o_wire_out(inj_o_wire_out_1755007813828_537)
        );
    assign inj_named_out_1755007813827_803 = inj_in_1755007813827_673;
    // END: module_with_param_ts1755007813827

    always_comb begin
        if (inj_sel_code_1755007813827_607 == 2'b00) begin
            inj_selected_data_1755007813827_530 = inj_data0_1755007813827_127;
        end else if (inj_sel_code_1755007813827_607 == 2'b01) begin
            inj_selected_data_1755007813827_530 = inj_data1_1755007813827_8;
        end else if (inj_sel_code_1755007813827_607 == 2'b10) begin
            inj_selected_data_1755007813827_530 = inj_data2_1755007813827_16;
        end else begin
            inj_selected_data_1755007813827_530 = inj_data3_1755007813827_372;
        end
    end
    // END: IfElseIfChain_ts1755007813827
endmodule

