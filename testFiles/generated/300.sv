module child_module_v1_config_dummy (
    input logic i,
    output logic o
);
    assign o = ~i; 
endmodule

module more_ops (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    output logic anded,
    output logic diff,
    output logic ored,
    output logic [7:0] sum,
    output logic xored
);
    assign sum = a + b;
    assign diff = a > c;
    assign anded = a & b;
    assign ored = a | c;
    assign xored = a ^ b;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_a_1755007855604_218,
    input logic [7:0] inj_b_1755007855604_946,
    input logic [7:0] inj_c_1755007855604_819,
    input logic inj_in_p_1755007855604_980,
    input logic inj_in_q_1755007855604_354,
    input int inj_in_val_1755007855604_973,
    input wire reset,
    output logic inj_anded_1755007855604_529,
    output logic [7:0] inj_data_a_out_task_1755007855605_891,
    output logic [7:0] inj_data_b_out_task_1755007855605_7,
    output logic [7:0] inj_data_out_1755007855604_98,
    output logic inj_diff_1755007855604_938,
    output logic inj_o_1755007855607_167,
    output logic inj_ored_1755007855604_104,
    output logic inj_out_r_1755007855604_715,
    output int inj_out_val_1755007855604_854,
    output logic [7:0] inj_sum_1755007855604_577,
    output logic [7:0] inj_x_aa_1755007855605_784,
    output logic inj_xored_1755007855604_14,
    output logic [7:0] inj_y_aa_1755007855605_453,
    output logic [7:0] inj_z_aa_1755007855605_320
);
    // BEGIN: super_outside_class_diag_mod_ts1755007855604
    // BEGIN: LintSensitiveList_ts1755007855604
    // BEGIN: SequentialLogic_ts1755007855604
    logic [7:0] internal_reg_ts1755007855604;
        // BEGIN: module_task_args_ts1755007855606
        logic [7:0] data_a_ts1755007855606 ;
        logic [7:0] data_b_ts1755007855606 ;
            child_module_v1_config_dummy child_module_v1_config_dummy_inst_1755007855607_7083 (
                .i(inj_in_q_1755007855604_354),
                .o(inj_o_1755007855607_167)
            );
        task automatic modify_vars;
            input logic [7:0] task_arg_ts1755007855606;
            logic [7:0] task_local_ts1755007855606 ;
            begin
                task_local_ts1755007855606 = task_arg_ts1755007855606;
                data_a_ts1755007855606 = task_local_ts1755007855606 + 8'd1;
                data_b_ts1755007855606 = task_arg_ts1755007855606 - 8'd1;
            end
        endtask
        always_comb begin
            if (inj_in_q_1755007855604_354) begin
                data_a_ts1755007855606 = internal_reg_ts1755007855604;
                data_b_ts1755007855606 = 8'hFF;
                modify_vars(inj_a_1755007855604_218);
            end else begin
                data_a_ts1755007855606 = 8'h00;
                data_b_ts1755007855606 = 8'h00;
            end
        end
        always_comb begin
            inj_data_a_out_task_1755007855605_891 = data_a_ts1755007855606 + 8'd2;
            inj_data_b_out_task_1755007855605_7 = data_b_ts1755007855606;
        end
        // END: module_task_args_ts1755007855606

        // BEGIN: split_combo_blocking_ts1755007855605
        always @(*) begin
            inj_x_aa_1755007855605_784 = inj_a_1755007855604_218 + inj_b_1755007855604_946;
            inj_y_aa_1755007855605_453 = inj_x_aa_1755007855605_784 - internal_reg_ts1755007855604;
            inj_z_aa_1755007855605_320 = inj_a_1755007855604_218 * internal_reg_ts1755007855604;
        end
        // END: split_combo_blocking_ts1755007855605

    always @(posedge clk or negedge reset) begin
        if (~reset) begin
            internal_reg_ts1755007855604 <= 8'h00;
        end else begin
            internal_reg_ts1755007855604 <= inj_a_1755007855604_218;
        end
    end
    assign inj_data_out_1755007855604_98 = internal_reg_ts1755007855604;
    // END: SequentialLogic_ts1755007855604

    more_ops more_ops_inst_1755007855604_12 (
        .a(inj_a_1755007855604_218),
        .b(inj_b_1755007855604_946),
        .c(inj_c_1755007855604_819),
        .anded(inj_anded_1755007855604_529),
        .diff(inj_diff_1755007855604_938),
        .ored(inj_ored_1755007855604_104),
        .sum(inj_sum_1755007855604_577),
        .xored(inj_xored_1755007855604_14)
    );
    always_comb begin
        inj_out_r_1755007855604_715 = inj_in_p_1755007855604_980 | inj_in_q_1755007855604_354;
    end
    // END: LintSensitiveList_ts1755007855604

    assign inj_out_val_1755007855604_854 = inj_in_val_1755007855604_973;
    // END: super_outside_class_diag_mod_ts1755007855604
endmodule

