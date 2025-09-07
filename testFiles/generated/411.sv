module snippet #(
    parameter bit GEN = 1
) (
    input wire clk,
    input logic inj_fs_in_target_1755007891677_449,
    input wire reset,
    output logic inj_fs_out_target_1755007891677_641,
    output logic inj_sig_out_1755007891677_140
);
    // BEGIN: mod_fixup_target_ts1755007891677
    // BEGIN: GenerateIfParam_ts1755007891677
    generate
        if (GEN) begin : g_true
            assign inj_sig_out_1755007891677_140 = inj_fs_in_target_1755007891677_449;
        end
        else begin : g_false
            assign inj_sig_out_1755007891677_140 = ~inj_fs_in_target_1755007891677_449;
        end
    endgenerate
    // END: GenerateIfParam_ts1755007891677

    assign inj_fs_out_target_1755007891677_641 = inj_fs_in_target_1755007891677_449;
    // END: mod_fixup_target_ts1755007891677
endmodule

