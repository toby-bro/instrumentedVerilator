module LintLatch (
    input logic in_j,
    input logic in_k,
    output logic out_l
);
    always_comb begin
        if (in_j) begin
            out_l = in_k;
        end else begin
            out_l = 1'b0; 
        end
    end
endmodule

module PragmaDiagnosticDirective (
    input int diag_input_val,
    output bit diag_output_flag
);
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
assign diag_output_flag = (diag_input_val > 0);
`ifdef SLANG_PRAGMA
`diagnostic pop
`endif
endmodule

module bind_module (
    input logic bind_in,
    output logic bind_out
);
    assign bind_out = bind_in;
endmodule

module snippet (
    input wire clk,
    input logic inj_bind_in_1755007875138_104,
    input int inj_diag_input_val_1755007875140_225,
    input logic inj_in_k_1755007875141_293,
    input logic [2:0] inj_in_shift_1755007875138_253,
    input logic [7:0] inj_in_val_1755007875138_701,
    input wire reset,
    output logic inj_bind_out_1755007875138_170,
    output wire inj_data_d_1755007875142_379,
    output reg inj_data_out_1755007875140_385,
    output bit inj_diag_output_flag_1755007875140_526,
    output logic inj_out_l_1755007875141_190,
    output logic [3:0] inj_out_part_1755007875138_629,
    output logic [7:0] inj_out_reg_1755007875138_160
);
    // BEGIN: module_assignments_in_loops_ts1755007875139
    localparam int PART_START = 4;
    localparam int PART_WIDTH = 4;
    logic [7:0] reg_var_ts1755007875139;
    logic [3:0] part_var_ts1755007875139;
        // BEGIN: simple_logic_b_ts1755007875142
        assign inj_data_d_1755007875142_379 = clk;
        // END: simple_logic_b_ts1755007875142

        LintLatch LintLatch_inst_1755007875141_6205 (
            .in_j(inj_bind_in_1755007875138_104),
            .in_k(inj_in_k_1755007875141_293),
            .out_l(inj_out_l_1755007875141_190)
        );
        // BEGIN: mod_event_posedge_ts1755007875140
        always @(posedge clk) begin
            inj_data_out_1755007875140_385 <= clk;
        end
        // END: mod_event_posedge_ts1755007875140

        PragmaDiagnosticDirective PragmaDiagnosticDirective_inst_1755007875140_8742 (
            .diag_input_val(inj_diag_input_val_1755007875140_225),
            .diag_output_flag(inj_diag_output_flag_1755007875140_526)
        );
    always_comb begin
        reg_var_ts1755007875139  = inj_in_val_1755007875138_701;
        part_var_ts1755007875139 = 4'h0;
        for (int i = 0; i < 4; i++) begin
            reg_var_ts1755007875139  = reg_var_ts1755007875139 + i;
            reg_var_ts1755007875139 += (i * 2);
            reg_var_ts1755007875139 <<= inj_in_shift_1755007875138_253;
            reg_var_ts1755007875139[i % 8] = (reg_var_ts1755007875139[i % 8] == 1'b0);
            reg_var_ts1755007875139[PART_START +: PART_WIDTH] = i[3:0];
        end
        part_var_ts1755007875139 = reg_var_ts1755007875139[7:4];
    end
    assign inj_out_reg_1755007875138_160  = reg_var_ts1755007875139;
    assign inj_out_part_1755007875138_629 = part_var_ts1755007875139;
    // END: module_assignments_in_loops_ts1755007875139

    bind_module bind_module_inst_1755007875138_7702 (
        .bind_out(inj_bind_out_1755007875138_170),
        .bind_in(inj_bind_in_1755007875138_104)
    );
endmodule

