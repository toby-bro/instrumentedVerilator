interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module ModuleLineDirective (
    input logic in1,
    output logic out1
);
    logic internal_sig_a;
    logic internal_sig_b;
    logic unused_line_var;
    `line 100 "virtual_file_A.sv" 1
    assign internal_sig_a = in1;
    `line 20 "virtual_file_B.sv" 1
    assign internal_sig_b = ~internal_sig_a;
    assign unused_line_var = 1'b1;
    `line 150 "virtual_file_A.sv" 2
    assign out1 = internal_sig_b;
    `line 1 "original_file.sv" 0
endmodule

module module_task_write (
    input logic [7:0] in_task_data,
    input logic task_en,
    output logic task_output_valid
);
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
        update_vif_signals(task_en, in_task_data, task_vif_inst.data, task_vif_inst.valid, task_vif_inst.ready);
        task_output_valid = task_vif_inst.valid;
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
    parameter integer UNUSED_PARAM = 8
) (
    input wire clk,
    input wire [15:0] inj_dcac_start_val_1755007810434_621,
    input logic [7:0] inj_i_target_data_1755007810432_435,
    input logic [3:0] inj_in_a_1755007810433_715,
    input logic [3:0] inj_in_b_1755007810433_975,
    input logic inj_in_m_1755007810432_338,
    input wire reset,
    output logic [15:0] inj_dcac_end_val_1755007810434_549,
    output logic inj_o_sum_1755007810432_825,
    output logic [7:0] inj_o_target_result_1755007810432_378,
    output logic inj_out1_1755007810443_469,
    output logic inj_out_n_1755007810432_270,
    output logic [3:0] inj_out_y_1755007810433_546,
    output logic inj_task_output_valid_1755007810433_479,
    output logic [7:0] inj_wide_reg_1755007810432_55
);
    // BEGIN: LintParamUnused_ts1755007810432
    // BEGIN: mod_lint_target_ts1755007810432
    logic l_reg_ts1755007810432;
        // BEGIN: deep_comb_assign_chain_ts1755007810441
        logic [15:0] t1_ts1755007810434, t2_ts1755007810434, t3_ts1755007810434, t4_ts1755007810434, t5_ts1755007810434, t6_ts1755007810434, t7_ts1755007810434, t8_ts1755007810434, t9_ts1755007810434, t10_ts1755007810434;
        logic [15:0] t11_ts1755007810434, t12_ts1755007810434, t13_ts1755007810434, t14_ts1755007810434, t15_ts1755007810434, t16_ts1755007810434, t17_ts1755007810434, t18_ts1755007810434, t19_ts1755007810434, t20_ts1755007810434;
        logic [15:0] t21_ts1755007810434, t22_ts1755007810434, t23_ts1755007810434, t24_ts1755007810434, t25_ts1755007810434, t26_ts1755007810434, t27_ts1755007810434, t28_ts1755007810434, t29_ts1755007810434, t30_ts1755007810434;
        logic [15:0] t31_ts1755007810434, t32_ts1755007810434, t33_ts1755007810434, t34_ts1755007810434, t35_ts1755007810434, t36_ts1755007810434, t37_ts1755007810434, t38_ts1755007810434, t39_ts1755007810434, t40_ts1755007810434;
            ModuleLineDirective ModuleLineDirective_inst_1755007810443_5477 (
                .in1(l_reg_ts1755007810432),
                .out1(inj_out1_1755007810443_469)
            );
        always_comb begin
            t1_ts1755007810434 = inj_dcac_start_val_1755007810434_621 + 1;
            t2_ts1755007810434 = t1_ts1755007810434 * 2;
            t3_ts1755007810434 = t2_ts1755007810434 - 3;
            t4_ts1755007810434 = t3_ts1755007810434 ^ 4;
            t5_ts1755007810434 = t4_ts1755007810434 | 5;
            t6_ts1755007810434 = t5_ts1755007810434 & 6;
            t7_ts1755007810434 = t6_ts1755007810434 + 7;
            t8_ts1755007810434 = t7_ts1755007810434 - 8;
            t9_ts1755007810434 = t8_ts1755007810434 ^ 9;
            t10_ts1755007810434 = t9_ts1755007810434 | 10;
            t11_ts1755007810434 = t10_ts1755007810434 & 11;
            t12_ts1755007810434 = t11_ts1755007810434 + 12;
            t13_ts1755007810434 = t12_ts1755007810434 - 13;
            t14_ts1755007810434 = t13_ts1755007810434 ^ 14;
            t15_ts1755007810434 = t14_ts1755007810434 | 15;
            t16_ts1755007810434 = t15_ts1755007810434 + 16;
            t17_ts1755007810434 = t16_ts1755007810434 * 17;
            t18_ts1755007810434 = t17_ts1755007810434 - 18;
            t19_ts1755007810434 = t18_ts1755007810434 ^ 19;
            t20_ts1755007810434 = t19_ts1755007810434 | 20;
            t21_ts1755007810434 = t20_ts1755007810434 + 1;
            t22_ts1755007810434 = t21_ts1755007810434 * 2;
            t23_ts1755007810434 = t22_ts1755007810434 - 3;
            t24_ts1755007810434 = t23_ts1755007810434 ^ 4;
            t25_ts1755007810434 = t24_ts1755007810434 | 5;
            t26_ts1755007810434 = t25_ts1755007810434 & 6;
            t27_ts1755007810434 = t26_ts1755007810434 + 7;
            t28_ts1755007810434 = t27_ts1755007810434 - 8;
            t29_ts1755007810434 = t28_ts1755007810434 ^ 9;
            t30_ts1755007810434 = t29_ts1755007810434 | 10;
            t31_ts1755007810434 = t30_ts1755007810434 & 11;
            t32_ts1755007810434 = t31_ts1755007810434 + 12;
            t33_ts1755007810434 = t32_ts1755007810434 - 13;
            t34_ts1755007810434 = t33_ts1755007810434 ^ 14;
            t35_ts1755007810434 = t34_ts1755007810434 | 15;
            t36_ts1755007810434 = t35_ts1755007810434 + 16;
            t37_ts1755007810434 = t36_ts1755007810434 * 17;
            t38_ts1755007810434 = t37_ts1755007810434 - 18;
            t39_ts1755007810434 = t38_ts1755007810434 ^ 19;
            t40_ts1755007810434 = t39_ts1755007810434 | 20;
            inj_dcac_end_val_1755007810434_549 = t40_ts1755007810434;
        end
        // END: deep_comb_assign_chain_ts1755007810441

        module_task_write module_task_write_inst_1755007810433_5128 (
            .in_task_data(inj_i_target_data_1755007810432_435),
            .task_en(l_reg_ts1755007810432),
            .task_output_valid(inj_task_output_valid_1755007810433_479)
        );
        // BEGIN: BitwiseAssign_ts1755007810433
        assign inj_out_y_1755007810433_546 = inj_in_a_1755007810433_715 ^ inj_in_b_1755007810433_975;
        // END: BitwiseAssign_ts1755007810433

        target_module_for_bind target_module_for_bind_inst_1755007810432_5484 (
            .i_target_clk(clk),
            .i_target_data(inj_i_target_data_1755007810432_435),
            .o_target_result(inj_o_target_result_1755007810432_378)
        );
    always_comb begin
        l_reg_ts1755007810432 = 1;
        inj_wide_reg_1755007810432_55 = {clk, reset};
    end
    assign inj_o_sum_1755007810432_825 = clk + reset;
    // END: mod_lint_target_ts1755007810432

    assign inj_out_n_1755007810432_270 = inj_in_m_1755007810432_338;
    // END: LintParamUnused_ts1755007810432
endmodule

