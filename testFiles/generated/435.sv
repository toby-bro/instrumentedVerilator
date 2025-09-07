module ModuleBasic (
    input logic a,
    input int b,
    output logic out_a,
    output int out_b
);
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c;
    int   d;
    always_comb begin
        logic temp_v;
        temp_v = d;
        c      = temp_v;
    end
    assign out_a = a;
    assign d     = b;
    assign out_b = d + P1 + LP1;
endmodule

module deep_logic (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    output logic [7:0] out
);
    assign out = (((a & b) | (~c)) ^ (a + b)) - (c << 2);
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_c_1755007899628_738,
    input logic [3:0] inj_data_in_n_1755007899626_754,
    input logic inj_i_1755007899626_893,
    input logic [7:0] inj_in1_z_1755007899626_846,
    input logic [7:0] inj_in2_z_1755007899626_511,
    input int inj_in_val_1755007899625_694,
    input wire reset,
    output logic [3:0] inj_data_out1_n_1755007899626_555,
    output logic [3:0] inj_data_out1_n_1755007899631_262,
    output logic [3:0] inj_data_out2_n_1755007899626_274,
    output logic [3:0] inj_data_out2_n_1755007899631_687,
    output logic [7:0] inj_data_out_1755007899629_317,
    output logic inj_named_out_1755007899626_74,
    output logic inj_o_1755007899626_839,
    output logic [7:0] inj_out1_z_1755007899626_714,
    output logic [7:0] inj_out2_z_1755007899626_426,
    output logic [7:0] inj_out_1755007899628_3,
    output logic inj_out_a_1755007899627_331,
    output int inj_out_b_1755007899627_571,
    output int inj_out_val_1755007899625_267
);
    // BEGIN: super_outside_class_diag_mod_ts1755007899625
    // BEGIN: child_module_v1_config_dummy_ts1755007899626
    // BEGIN: module_with_param_ts1755007899626
    parameter int DELAY = 10;
    logic bind_dummy_in_ts1755007899626;
    logic bind_dummy_out_ts1755007899626;
        // BEGIN: split_multiple_blocking_ts1755007899626
        logic [3:0] temp_n_ts1755007899626;
            // BEGIN: SequentialLogic_ts1755007899630
            logic [7:0] internal_reg_ts1755007899630;
                // BEGIN: split_multiple_blocking_ts1755007899631
                logic [3:0] temp_n_ts1755007899631;
                always @(*) begin
                    temp_n_ts1755007899631 = inj_data_in_n_1755007899626_754 + 1;
                    inj_data_out1_n_1755007899631_262 = temp_n_ts1755007899631 * 2;
                    inj_data_out2_n_1755007899631_687 = temp_n_ts1755007899631 + 3;
                end
                // END: split_multiple_blocking_ts1755007899631

            always @(posedge clk or negedge reset) begin
                if (~reset) begin
                    internal_reg_ts1755007899630 <= 8'h00;
                end else begin
                    internal_reg_ts1755007899630 <= inj_in2_z_1755007899626_511;
                end
            end
            assign inj_data_out_1755007899629_317 = internal_reg_ts1755007899630;
            // END: SequentialLogic_ts1755007899630

            deep_logic deep_logic_inst_1755007899628_9180 (
                .b(inj_in1_z_1755007899626_846),
                .c(inj_c_1755007899628_738),
                .out(inj_out_1755007899628_3),
                .a(inj_in2_z_1755007899626_511)
            );
            ModuleBasic ModuleBasic_inst_1755007899627_7761 (
                .out_b(inj_out_b_1755007899627_571),
                .a(bind_dummy_in_ts1755007899626),
                .b(inj_in_val_1755007899625_694),
                .out_a(inj_out_a_1755007899627_331)
            );
            // BEGIN: split_diff_vars_branches_ts1755007899627
            always @(posedge clk) begin
                if (inj_i_1755007899626_893) begin
                    inj_out1_z_1755007899626_714 <= inj_in1_z_1755007899626_846;
                end else begin
                    inj_out2_z_1755007899626_426 <= inj_in2_z_1755007899626_511;
                end
            end
            // END: split_diff_vars_branches_ts1755007899627

        always @(*) begin
            temp_n_ts1755007899626 = inj_data_in_n_1755007899626_754 + 1;
            inj_data_out1_n_1755007899626_555 = temp_n_ts1755007899626 * 2;
            inj_data_out2_n_1755007899626_274 = temp_n_ts1755007899626 + 3;
        end
        // END: split_multiple_blocking_ts1755007899626

    assign inj_named_out_1755007899626_74 = inj_i_1755007899626_893;
    // END: module_with_param_ts1755007899626

    assign inj_o_1755007899626_839 = ~inj_i_1755007899626_893; 
    // END: child_module_v1_config_dummy_ts1755007899626

    assign inj_out_val_1755007899625_267 = inj_in_val_1755007899625_694;
    // END: super_outside_class_diag_mod_ts1755007899625
endmodule

