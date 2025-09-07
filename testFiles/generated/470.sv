module LintImplicitWidth (
    input logic [7:0] in_wide,
    output logic [3:0] out_narrow
);
    assign out_narrow = in_wide;
endmodule

module snippet (
    input wire clk,
    input bit inj_in_1755007911274_982,
    input logic [7:0] inj_in_wide_1755007911274_537,
    input wire reset,
    output bit inj_out_1755007911274_434,
    output logic [3:0] inj_out_narrow_1755007911274_441
);
    // BEGIN: BindSimpleModule_ts1755007911274
    assign inj_out_1755007911274_434 = inj_in_1755007911274_982;
    // END: BindSimpleModule_ts1755007911274

    LintImplicitWidth LintImplicitWidth_inst_1755007911274_363 (
        .out_narrow(inj_out_narrow_1755007911274_441),
        .in_wide(inj_in_wide_1755007911274_537)
    );
endmodule

