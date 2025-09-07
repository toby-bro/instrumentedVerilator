module BindSimpleModule (
    input bit in,
    output bit out
);
    assign out = in;
endmodule

module snippet (
    input wire clk,
    input bit inj_in_1755007837124_830,
    input logic [3:0] inj_v1_1755007837124_109,
    input logic [3:0] inj_v2_1755007837124_511,
    input wire reset,
    output logic inj_eq_1755007837124_229,
    output bit inj_out_1755007837124_955
);
    // BEGIN: ModCompareVec_ts1755007837124
    BindSimpleModule BindSimpleModule_inst_1755007837124_5563 (
        .in(inj_in_1755007837124_830),
        .out(inj_out_1755007837124_955)
    );
    assign inj_eq_1755007837124_229 = (inj_v1_1755007837124_109 == inj_v2_1755007837124_511);
    // END: ModCompareVec_ts1755007837124
endmodule

