module mod_named_begin (
    input int data_in,
    output int data_out
);
    always_comb begin : my_named_block
        data_out = data_in;
    end
endmodule

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module snippet (
    input wire clk,
    input logic inj_d_1755007838082_537,
    input int inj_data_in_1755007838082_478,
    input bit [7:0] inj_data_in_1755007838084_576,
    input logic [3:0] inj_i_bind_control_1755007838082_504,
    input bit inj_select_signal_1755007838084_196,
    input wire reset,
    output int inj_data_out_1755007838082_914,
    output bit [7:0] inj_data_out_1755007838084_202,
    output int inj_data_out_1755007838085_365,
    output bit inj_diag_output_flag_1755007838084_700,
    output logic inj_o_bind_status_1755007838082_74,
    output logic inj_q_1755007838082_331
);
    // BEGIN: ModClockedResetReg_ts1755007838083
    // BEGIN: SimpleLogicTest_ts1755007838084
    logic [7:0] temp_data_ts1755007838084;
        mod_named_begin mod_named_begin_inst_1755007838085_5415 (
            .data_in(inj_data_in_1755007838082_478),
            .data_out(inj_data_out_1755007838085_365)
        );
        // BEGIN: PragmaDiagnosticDirective_ts1755007838084
    `ifdef SLANG_PRAGMA
    `diagnostic push
    `endif
    `ifdef SLANG_PRAGMA
    `diagnostic ignore "SLANG_UNUSED_VARIABLE"
    `endif
    `ifdef SLANG_PRAGMA
    `diagnostic warn "SLANG_IMPLICIT_CAST"
    `endif
    `ifdef SLANG_PRAGMA
    `diagnostic error "SLANG_MULTIPLE_DRIVER"
    `endif
    `ifdef SLANG_PRAGMA
    `diagnostic fatal "SLANG_SYNTAX_ERROR_FATAL"
    `endif
    `ifdef SLANG_PRAGMA
    `diagnostic ignore (value=("SLANG_UNDRIVEN_SIGNAL", "SLANG_UNREAD_SIGNAL"))
    `endif
    `ifdef SLANG_PRAGMA
    `diagnostic warn (value="SLANG_LATCH_INFERRED")
    `endif
    assign inj_diag_output_flag_1755007838084_700 = (inj_data_in_1755007838082_478 > 0);
    `ifdef SLANG_PRAGMA
    `diagnostic pop
    `endif
        // END: PragmaDiagnosticDirective_ts1755007838084

    always_comb begin
        if (inj_select_signal_1755007838084_196) begin
            temp_data_ts1755007838084 = inj_data_in_1755007838084_576 + 1;
        end else begin
            temp_data_ts1755007838084 = inj_data_in_1755007838084_576 - 1;
        end
        inj_data_out_1755007838084_202 = temp_data_ts1755007838084;
    end
    // END: SimpleLogicTest_ts1755007838084

    always @(posedge clk or negedge reset) begin
    if (!reset) begin
        inj_q_1755007838082_331 <= 1'b0;
    end else begin
        inj_q_1755007838082_331 <= inj_d_1755007838082_537;
    end
    end
    // END: ModClockedResetReg_ts1755007838083

    module_to_bind module_to_bind_inst_1755007838082_661 (
        .o_bind_status(inj_o_bind_status_1755007838082_74),
        .i_bind_clk(clk),
        .i_bind_control(inj_i_bind_control_1755007838082_504)
    );
    mod_named_begin mod_named_begin_inst_1755007838082_8531 (
        .data_in(inj_data_in_1755007838082_478),
        .data_out(inj_data_out_1755007838082_914)
    );
endmodule

