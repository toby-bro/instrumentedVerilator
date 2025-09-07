module module_with_param (
    input logic in,
    output logic named_out
);
    parameter int DELAY = 10;
    logic bind_dummy_in;
    logic bind_dummy_out;
    assign named_out = in;
endmodule

module snippet #(
    parameter integer UNUSED_PARAM = 8
) (
    input wire clk,
    input logic [7:0] inj_data_in_1755007765547_318,
    input logic inj_nm_in_1755007765547_383,
    input wire reset,
    output logic inj_named_out_1755007765548_131,
    output logic inj_nm_out_1755007765547_567,
    output logic [7:0] inj_out_mv_a_1755007765547_228,
    output logic [7:0] inj_out_mv_b_1755007765547_998,
    output logic [7:0] inj_out_mv_c_1755007765547_363,
    output logic inj_out_n_1755007765548_721
);
    // BEGIN: nested_module_ts1755007765547
    // BEGIN: mod_split_multiple_vars_ts1755007765547
    logic [7:0]  split_mv_var_ts1755007765547;
    logic [7:0] other_mv_var1_ts1755007765547;
    logic [7:0] other_mv_var2_ts1755007765547;
        module_with_param module_with_param_inst_1755007765548_3107 (
            .named_out(inj_named_out_1755007765548_131),
            .in(inj_nm_in_1755007765547_383)
        );
        // BEGIN: LintParamUnused_ts1755007765548
        assign inj_out_n_1755007765548_721 = inj_nm_in_1755007765547_383;
        // END: LintParamUnused_ts1755007765548

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_mv_var_ts1755007765547 <= 8'b0;
            other_mv_var1_ts1755007765547 <= 8'b0;
            other_mv_var2_ts1755007765547 <= 8'b0;
        end else begin
            split_mv_var_ts1755007765547 <= inj_data_in_1755007765547_318;
            other_mv_var1_ts1755007765547 <= inj_data_in_1755007765547_318 + 1;
            other_mv_var2_ts1755007765547 <= inj_data_in_1755007765547_318 + 2;
            if (inj_data_in_1755007765547_318 > 100) begin
                split_mv_var_ts1755007765547 <= 8'hFF;
            end
            inj_out_mv_a_1755007765547_228 <= split_mv_var_ts1755007765547;
            inj_out_mv_b_1755007765547_998 <= other_mv_var1_ts1755007765547;
            inj_out_mv_c_1755007765547_363 <= other_mv_var2_ts1755007765547;
        end
    end
    // END: mod_split_multiple_vars_ts1755007765547

    assign inj_nm_out_1755007765547_567 = inj_nm_in_1755007765547_383;
    // END: nested_module_ts1755007765547
endmodule

