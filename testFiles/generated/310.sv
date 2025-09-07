module ConcatVectorOps (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [7:0] c,
    output logic [15:0] out_concat
);
    assign out_concat = {a, b, c};
endmodule

module snippet (
    input wire clk,
    input int inj_in_val_1755007858724_320,
    input logic [7:0] inj_in_val_1755007858725_75,
    input logic [3:0] inj_v1_1755007858726_139,
    input logic [3:0] inj_v2_1755007858726_789,
    input wire reset,
    output logic inj_eq_1755007858726_628,
    output logic [15:0] inj_out_concat_1755007858726_335,
    output int inj_out_val_1755007858724_679,
    output logic [7:0] inj_out_val_1755007858725_845
);
    // BEGIN: local_not_allowed_diag_mod_ts1755007858724
    // BEGIN: generic_class_scope_diag_mod_ts1755007858725
    // BEGIN: ModCompareVec_ts1755007858726
    ConcatVectorOps ConcatVectorOps_inst_1755007858726_5808 (
        .a(inj_v1_1755007858726_139),
        .b(inj_v2_1755007858726_789),
        .c(inj_in_val_1755007858725_75),
        .out_concat(inj_out_concat_1755007858726_335)
    );
    assign inj_eq_1755007858726_628 = (inj_v1_1755007858726_139 == inj_v2_1755007858726_789);
    // END: ModCompareVec_ts1755007858726

    assign inj_out_val_1755007858725_845 = inj_in_val_1755007858725_75;
    // END: generic_class_scope_diag_mod_ts1755007858725

    assign inj_out_val_1755007858724_679 = inj_in_val_1755007858724_320;
    // END: local_not_allowed_diag_mod_ts1755007858724
endmodule

