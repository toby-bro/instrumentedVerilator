module mod_fixup_target (
    input logic fs_in_target,
    output logic fs_out_target
);
    assign fs_out_target = fs_in_target;
endmodule

module snippet (
    input wire clk,
    input logic inj_fs_in_target_1755007856542_571,
    input wire reset,
    output logic inj_fs_out_target_1755007856542_364
);
    mod_fixup_target mod_fixup_target_inst_1755007856542_3327 (
        .fs_out_target(inj_fs_out_target_1755007856542_364),
        .fs_in_target(inj_fs_in_target_1755007856542_571)
    );
endmodule

