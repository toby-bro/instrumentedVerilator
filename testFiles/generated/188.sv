module mod_logical_not (
    input logic cond_in,
    output logic cond_out
);
    always_comb begin
        cond_out = !cond_in;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_bind_in_1755007816095_765,
    input logic [7:0] inj_in_v_1755007816095_933,
    input logic [15:0] inj_packed_in_1755007816095_568,
    input wire reset,
    output logic inj_bind_out_1755007816095_130,
    output logic [7:0] inj_byte_out_1755007816095_619,
    output logic inj_cond_out_1755007816095_561,
    output logic [7:0] inj_out_v_1755007816095_258,
    output logic [15:0] inj_packed_out_1755007816095_223
);
    // BEGIN: ModVectorAdd_ts1755007816095
    // BEGIN: bind_module_ts1755007816095
    // BEGIN: PackedStructOps_ts1755007816095
    typedef struct packed {
        logic [7:0] low_ts1755007816095;
        logic [7:0] high_ts1755007816095;
    } pair_t;
    pair_t data_pair;
    assign data_pair.high_ts1755007816095 = inj_packed_in_1755007816095_568[15:8];
    assign data_pair.low_ts1755007816095 = inj_in_v_1755007816095_933;
    assign inj_byte_out_1755007816095_619 = data_pair.high_ts1755007816095;
    assign inj_packed_out_1755007816095_223[15:8] = data_pair.high_ts1755007816095;
    assign inj_packed_out_1755007816095_223[7:0] = data_pair.low_ts1755007816095 + inj_in_v_1755007816095_933;
    // END: PackedStructOps_ts1755007816095

    mod_logical_not mod_logical_not_inst_1755007816095_1113 (
        .cond_in(inj_bind_in_1755007816095_765),
        .cond_out(inj_cond_out_1755007816095_561)
    );
    assign inj_bind_out_1755007816095_130 = inj_bind_in_1755007816095_765;
    // END: bind_module_ts1755007816095

    assign inj_out_v_1755007816095_258 = inj_in_v_1755007816095_933 + 8'h01;
    // END: ModVectorAdd_ts1755007816095
endmodule

