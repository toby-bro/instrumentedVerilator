module snippet (
    input wire clk,
    input logic inj_in1_bind_def_1755007879979_398,
    input logic inj_in_q_1755007879979_491,
    input wire reset,
    output logic inj_out1_bind_def_1755007879979_11,
    output logic inj_out_r_1755007879979_69
);
    // BEGIN: mod_basic_bind_ts1755007879979
    // BEGIN: LintSensitiveList_ts1755007879980
    always_comb begin
        inj_out_r_1755007879979_69 = inj_in1_bind_def_1755007879979_398 | inj_in_q_1755007879979_491;
    end
    // END: LintSensitiveList_ts1755007879980

    assign inj_out1_bind_def_1755007879979_11 = ~inj_in1_bind_def_1755007879979_398;
    // END: mod_basic_bind_ts1755007879979
endmodule

