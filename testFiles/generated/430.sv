module GenerateIfParam #(
    parameter bit GEN = 1
) (
    input logic sig_in,
    output logic sig_out
);
    generate
        if (GEN) begin : g_true
            assign sig_out = sig_in;
        end
        else begin : g_false
            assign sig_out = ~sig_in;
        end
    endgenerate
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_d0_w_1755007898080_53,
    input logic [7:0] inj_d1_w_1755007898080_720,
    input logic [7:0] inj_d2_w_1755007898080_906,
    input logic [7:0] inj_d3_w_1755007898080_947,
    input logic inj_i_data_in_1755007898082_991,
    input logic inj_i_write_en_1755007898082_850,
    input logic [1:0] inj_sel_w_1755007898080_992,
    input wire reset,
    output logic [7:0] inj_data_a_out_task_1755007898084_209,
    output logic [7:0] inj_data_b_out_task_1755007898084_93,
    output logic inj_dummy_out_1755007898083_940,
    output logic inj_o_done_ni_1755007898085_155,
    output logic inj_o_forceable_signal_1755007898082_746,
    output logic inj_o_read_signal_1755007898082_687,
    output logic [7:0] inj_out_data_1755007898083_675,
    output logic inj_out_valid_1755007898083_669,
    output logic [7:0] inj_out_w_1755007898080_383,
    output logic inj_sig_out_1755007898083_646
);
    // BEGIN: split_case_ts1755007898081
    // BEGIN: module_forceable_attr_ts1755007898083
    logic forceable_signal_ts1755007898082 ;
    logic read_internal_ts1755007898082;
        // BEGIN: module_task_args_ts1755007898084
        logic [7:0] data_a_ts1755007898084 ;
        logic [7:0] data_b_ts1755007898084 ;
            // BEGIN: mod_no_inline_module_ts1755007898085
            logic r_toggle = 1'b0;
            always_ff @(posedge reset) begin
                r_toggle <= ~r_toggle;
            end
            assign inj_o_done_ni_1755007898085_155 = r_toggle;
            // END: mod_no_inline_module_ts1755007898085

        task automatic modify_vars;
            input logic [7:0] task_arg_ts1755007898084;
            logic [7:0] task_local_ts1755007898084 ;
            begin
                task_local_ts1755007898084 = task_arg_ts1755007898084;
                data_a_ts1755007898084 = task_local_ts1755007898084 + 8'd1;
                data_b_ts1755007898084 = task_arg_ts1755007898084 - 8'd1;
            end
        endtask
        always_comb begin
            if (forceable_signal_ts1755007898082) begin
                data_a_ts1755007898084 = inj_d1_w_1755007898080_720;
                data_b_ts1755007898084 = 8'hFF;
                modify_vars(inj_d0_w_1755007898080_53);
            end else begin
                data_a_ts1755007898084 = 8'h00;
                data_b_ts1755007898084 = 8'h00;
            end
        end
        always_comb begin
            inj_data_a_out_task_1755007898084_209 = data_a_ts1755007898084 + 8'd2;
            inj_data_b_out_task_1755007898084_93 = data_b_ts1755007898084;
        end
        // END: module_task_args_ts1755007898084

        // BEGIN: virtual_interface_lookup_mod_ts1755007898083
        always_comb begin
            inj_out_data_1755007898083_675  = inj_d0_w_1755007898080_53;
            inj_out_valid_1755007898083_669 = forceable_signal_ts1755007898082;
            inj_dummy_out_1755007898083_940 = inj_i_data_in_1755007898082_991;
        end
        // END: virtual_interface_lookup_mod_ts1755007898083

        GenerateIfParam GenerateIfParam_inst_1755007898083_3383 (
            .sig_out(inj_sig_out_1755007898083_646),
            .sig_in(read_internal_ts1755007898082)
        );
    assign inj_o_forceable_signal_1755007898082_746 = forceable_signal_ts1755007898082;
    always @(posedge clk or negedge reset) begin
        if (!reset) begin
            forceable_signal_ts1755007898082 <= 1'b0;
            read_internal_ts1755007898082 <= 1'b0;
        end else begin
            if (inj_i_write_en_1755007898082_850) begin
                forceable_signal_ts1755007898082 <= inj_i_data_in_1755007898082_991;
            end
            read_internal_ts1755007898082 <= forceable_signal_ts1755007898082;
        end
    end
    assign inj_o_read_signal_1755007898082_687 = read_internal_ts1755007898082;
    // END: module_forceable_attr_ts1755007898083

    always @(posedge clk) begin
        case (inj_sel_w_1755007898080_992)
            2'b00: inj_out_w_1755007898080_383 <= inj_d0_w_1755007898080_53;
            2'b01: inj_out_w_1755007898080_383 <= inj_d1_w_1755007898080_720;
            2'b10: inj_out_w_1755007898080_383 <= inj_d2_w_1755007898080_906;
            default: inj_out_w_1755007898080_383 <= inj_d3_w_1755007898080_947;
        endcase
    end
    // END: split_case_ts1755007898081
endmodule

