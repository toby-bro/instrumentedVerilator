module ContinuousWire (
    input logic din,
    output wire dout
);
    wire internal_w;
    assign internal_w = din;
    assign dout       = internal_w;
endmodule

module LintParamUnused #(
    parameter integer UNUSED_PARAM = 8
) (
    input logic in_m,
    output logic out_n
);
    assign out_n = in_m;
endmodule

module simple_undeclared_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module snippet (
    input wire clk,
    input logic inj_din_1755007904619_266,
    input logic [3:0] inj_in_h_1755007904619_698,
    input logic [3:0] inj_in_l_1755007904619_475,
    input int inj_in_val_1755007904619_744,
    input wire reset,
    output wire inj_dout_1755007904619_66,
    output logic [7:0] inj_out_c_1755007904619_361,
    output logic inj_out_n_1755007904619_39,
    output int inj_out_val_1755007904619_696
);
    // BEGIN: concat_op_ts1755007904619
    simple_undeclared_mod simple_undeclared_mod_inst_1755007904619_958 (
        .in_val(inj_in_val_1755007904619_744),
        .out_val(inj_out_val_1755007904619_696)
    );
    LintParamUnused LintParamUnused_inst_1755007904619_256 (
        .in_m(inj_din_1755007904619_266),
        .out_n(inj_out_n_1755007904619_39)
    );
    assign inj_out_c_1755007904619_361 = {inj_in_h_1755007904619_698, inj_in_l_1755007904619_475};
    // END: concat_op_ts1755007904619

    ContinuousWire ContinuousWire_inst_1755007904619_4312 (
        .dout(inj_dout_1755007904619_66),
        .din(inj_din_1755007904619_266)
    );
endmodule

