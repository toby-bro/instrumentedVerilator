module Module_ConfigKeywords (
    input bit cfg_in,
    output bit cfg_out
);
    assign cfg_out = cfg_in;
endmodule

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

module comb_conditional (
    input bit [7:0] data1,
    input bit [7:0] data2,
    input bit sel,
    output bit [7:0] result1,
    output bit [7:0] result2
);
    always @* begin
        if (sel) begin
            result1 = data1;
            result2 = data1;
        end else begin
            result1 = data2;
            result2 = data2;
        end
    end
endmodule

module explicit_non_ansi_ports_module (
    dummy_in_non_ansi,
    named_conn_in,
    dummy_out_non_ansi,
    named_conn_out
);
    input logic named_conn_in;
    output logic named_conn_out;
    input logic dummy_in_non_ansi;
    output logic dummy_out_non_ansi;
    assign named_conn_out = named_conn_in;
    assign dummy_out_non_ansi = dummy_in_non_ansi;
endmodule

module generic_class_scope_diag_mod (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    assign out_val = in_val;
endmodule

module macro_concat_user (
    input logic [3:0] concat_in,
    output logic [7:0] concat_out
);
    `define MAKE_NAME(a,b) a``b
    logic var_signal;
    always_comb begin
        `MAKE_NAME(var,_signal) = concat_in[0];
    end
    assign concat_out = {4'b0, concat_in[3:1], var_signal};
endmodule

module snippet #(
    parameter integer UNUSED_PARAM = 8
) (
    input wire clk,
    input logic [3:0] inj_concat_in_1755007798522_831,
    input logic inj_cond1_m_1755007798521_680,
    input logic inj_cond2_m_1755007798521_525,
    input bit [7:0] inj_data1_1755007798524_723,
    input bit [7:0] inj_data2_1755007798524_313,
    input logic [2:0] inj_in_val_1755007798521_977,
    input bit inj_sel_1755007798524_314,
    input int inj_val_a_1755007798532_787,
    input logic [7:0] inj_val_a_m_1755007798521_157,
    input int inj_val_b_1755007798532_883,
    input logic [7:0] inj_val_b_m_1755007798521_346,
    input int inj_val_c_1755007798532_45,
    input logic [7:0] inj_val_c_m_1755007798521_11,
    input wire reset,
    output bit inj_cfg_out_1755007798525_105,
    output logic [7:0] inj_concat_out_1755007798522_385,
    output logic [7:0] inj_data_a_out_task_1755007798526_16,
    output logic [7:0] inj_data_b_out_task_1755007798526_569,
    output logic [7:0] inj_data_out_1755007798529_818,
    output logic inj_dout_1755007798521_505,
    output logic inj_dummy_out_non_ansi_1755007798521_608,
    output logic inj_extra_out_1755007798524_647,
    output logic [5:0] inj_indicators_1755007798532_803,
    output logic inj_named_conn_out_1755007798521_815,
    output logic inj_out1_1755007798524_494,
    output logic inj_out2_1755007798524_780,
    output logic inj_out_n_1755007798523_752,
    output reg inj_out_res_1755007798521_231,
    output logic [7:0] inj_out_val_1755007798530_543,
    output bit [7:0] inj_result1_1755007798524_837,
    output bit [7:0] inj_result2_1755007798524_859,
    output logic [7:0] inj_result_m_1755007798521_838
);
    // BEGIN: split_nested_if_ts1755007798521
    // BEGIN: ModRegister_ts1755007798521
    // BEGIN: LintParamUnused_ts1755007798523
    // BEGIN: ansi_implicit_inherit_ts1755007798525
    // BEGIN: module_task_args_ts1755007798527
    logic [7:0] data_a_ts1755007798527 ;
    logic [7:0] data_b_ts1755007798527 ;
        // BEGIN: dup_compare_ts1755007798533
        always_comb begin
            inj_indicators_1755007798532_803 = '0;
            inj_indicators_1755007798532_803[0] = (inj_val_a_1755007798532_787 == inj_val_b_1755007798532_883);
            inj_indicators_1755007798532_803[1] = (inj_val_a_1755007798532_787 != inj_val_b_1755007798532_883);
            inj_indicators_1755007798532_803[2] = (inj_val_a_1755007798532_787 > inj_val_b_1755007798532_883);
            inj_indicators_1755007798532_803[3] = (inj_val_a_1755007798532_787 < inj_val_b_1755007798532_883);
            inj_indicators_1755007798532_803[4] = (inj_val_a_1755007798532_787 >= inj_val_b_1755007798532_883);
            inj_indicators_1755007798532_803[5] = (inj_val_a_1755007798532_787 <= inj_val_b_1755007798532_883);
            if (inj_val_b_1755007798532_883 == inj_val_c_1755007798532_45) begin
                inj_indicators_1755007798532_803 = inj_indicators_1755007798532_803 | 6'b111111;
            end
            if (inj_val_a_1755007798532_787 > inj_val_c_1755007798532_45) begin
                inj_indicators_1755007798532_803 = inj_indicators_1755007798532_803 & 6'b000000;
            end
            if ((inj_val_a_1755007798532_787 < inj_val_b_1755007798532_883) && (inj_val_b_1755007798532_883 > inj_val_c_1755007798532_45)) begin
                inj_indicators_1755007798532_803[0] = 1;
            end else if ((inj_val_a_1755007798532_787 >= inj_val_b_1755007798532_883) || (inj_val_b_1755007798532_883 <= inj_val_c_1755007798532_45)) begin
                inj_indicators_1755007798532_803[1] = 1;
            end
        end
        // END: dup_compare_ts1755007798533

        generic_class_scope_diag_mod generic_class_scope_diag_mod_inst_1755007798530_1407 (
            .in_val(data_a_ts1755007798527),
            .out_val(inj_out_val_1755007798530_543)
        );
        // BEGIN: sequential_register_en_ts1755007798529
        always_ff @(posedge clk) begin
            if (inj_cond1_m_1755007798521_680) begin
                inj_data_out_1755007798529_818 <= data_a_ts1755007798527;
            end
        end
        // END: sequential_register_en_ts1755007798529

    task automatic modify_vars;
        input logic [7:0] task_arg_ts1755007798527;
        logic [7:0] task_local_ts1755007798527 ;
        begin
            task_local_ts1755007798527 = task_arg_ts1755007798527;
            data_a_ts1755007798527 = task_local_ts1755007798527 + 8'd1;
            data_b_ts1755007798527 = task_arg_ts1755007798527 - 8'd1;
        end
    endtask
    always_comb begin
        if (inj_cond1_m_1755007798521_680) begin
            data_a_ts1755007798527 = inj_val_b_m_1755007798521_346;
            data_b_ts1755007798527 = 8'hFF;
            modify_vars(inj_val_a_m_1755007798521_157);
        end else begin
            data_a_ts1755007798527 = 8'h00;
            data_b_ts1755007798527 = 8'h00;
        end
    end
    always_comb begin
        inj_data_a_out_task_1755007798526_16 = data_a_ts1755007798527 + 8'd2;
        inj_data_b_out_task_1755007798526_569 = data_b_ts1755007798527;
    end
    // END: module_task_args_ts1755007798527

    Module_ConfigKeywords Module_ConfigKeywords_inst_1755007798525_2517 (
        .cfg_in(inj_sel_1755007798524_314),
        .cfg_out(inj_cfg_out_1755007798525_105)
    );
    always_comb begin
        inj_out1_1755007798524_494 = |inj_in_val_1755007798521_977;
        inj_out2_1755007798524_780 = |inj_cond1_m_1755007798521_680;
        inj_extra_out_1755007798524_647 = inj_out1_1755007798524_494 ^ inj_out2_1755007798524_780;
    end
    // END: ansi_implicit_inherit_ts1755007798525

    comb_conditional comb_conditional_inst_1755007798524_6359 (
        .data2(inj_data2_1755007798524_313),
        .sel(inj_sel_1755007798524_314),
        .result1(inj_result1_1755007798524_837),
        .result2(inj_result2_1755007798524_859),
        .data1(inj_data1_1755007798524_723)
    );
    assign inj_out_n_1755007798523_752 = inj_cond2_m_1755007798521_525;
    // END: LintParamUnused_ts1755007798523

    macro_concat_user macro_concat_user_inst_1755007798522_4704 (
        .concat_in(inj_concat_in_1755007798522_831),
        .concat_out(inj_concat_out_1755007798522_385)
    );
    casez_xz_alt casez_xz_alt_inst_1755007798521_9245 (
        .in_val(inj_in_val_1755007798521_977),
        .out_res(inj_out_res_1755007798521_231)
    );
    explicit_non_ansi_ports_module explicit_non_ansi_ports_module_inst_1755007798521_6569 (
        .dummy_in_non_ansi(inj_cond1_m_1755007798521_680),
        .dummy_out_non_ansi(inj_dummy_out_non_ansi_1755007798521_608),
        .named_conn_in(inj_cond2_m_1755007798521_525),
        .named_conn_out(inj_named_conn_out_1755007798521_815)
    );
    always @* begin
        inj_dout_1755007798521_505 = inj_cond1_m_1755007798521_680;
    end
    // END: ModRegister_ts1755007798521

    always @(posedge clk) begin
        if (inj_cond1_m_1755007798521_680) begin
            if (inj_cond2_m_1755007798521_525) begin
                inj_result_m_1755007798521_838 <= inj_val_a_m_1755007798521_157;
            end else begin
                inj_result_m_1755007798521_838 <= inj_val_b_m_1755007798521_346;
            end
        end else begin
            inj_result_m_1755007798521_838 <= inj_val_c_m_1755007798521_11;
        end
    end
    // END: split_nested_if_ts1755007798521
endmodule

