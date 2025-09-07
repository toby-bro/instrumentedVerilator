module sub_inst_array_mod (
    input logic [7:0] in,
    output logic [7:0] out
);
    assign out = in;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_in_1755007900615_152,
    input wire reset,
    output logic [7:0] inj_out_1755007900615_8,
    output logic [7:0] inj_out_var_1755007900615_857
);
    // BEGIN: not_a_hierarchical_scope_diag_mod_ts1755007900615
    logic [7:0] simple_var_nahsdm_ts1755007900615;
    always_comb simple_var_nahsdm_ts1755007900615 = inj_in_1755007900615_152;
    assign inj_out_var_1755007900615_857 = simple_var_nahsdm_ts1755007900615;
    // END: not_a_hierarchical_scope_diag_mod_ts1755007900615

    sub_inst_array_mod sub_inst_array_mod_inst_1755007900615_743 (
        .in(inj_in_1755007900615_152),
        .out(inj_out_1755007900615_8)
    );
endmodule

