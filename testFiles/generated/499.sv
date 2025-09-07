module mod_seq_reg (
    input logic clk,
    input logic d,
    output logic q
);
    always_ff @(posedge clk) begin
        q <= d;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_in_c_1755007920952_216,
    input logic inj_in_d_1755007920952_563,
    input int inj_in_val_1755007920952_577,
    input wire reset,
    output logic inj_out_e_1755007920952_820,
    output logic inj_out_r_1755007920953_135,
    output int inj_out_val_1755007920952_213,
    output logic inj_q_1755007920952_547
);
    // BEGIN: LintCombBlockAssign_ts1755007920952
    // BEGIN: undeclared_but_found_pkg_diag_mod_ts1755007920952
    // BEGIN: LintSensitiveList_ts1755007920953
    always_comb begin
        inj_out_r_1755007920953_135 = inj_in_d_1755007920952_563 | inj_in_c_1755007920952_216;
    end
    // END: LintSensitiveList_ts1755007920953

    mod_seq_reg mod_seq_reg_inst_1755007920952_4777 (
        .d(inj_in_c_1755007920952_216),
        .q(inj_q_1755007920952_547),
        .clk(clk)
    );
    assign inj_out_val_1755007920952_213 = inj_in_val_1755007920952_577;
    // END: undeclared_but_found_pkg_diag_mod_ts1755007920952

    always_comb begin
        inj_out_e_1755007920952_820 = inj_in_c_1755007920952_216 & inj_in_d_1755007920952_563;
    end
    // END: LintCombBlockAssign_ts1755007920952
endmodule

