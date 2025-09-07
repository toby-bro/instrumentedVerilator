module mod_fixup_target (
    input logic fs_in_target,
    output logic fs_out_target
);
    assign fs_out_target = fs_in_target;
endmodule

module mod_fixup_syntax_user (
    input logic fs_in,
    output wire fs_out
);
    logic fixup_out_val;
    mod_fixup_target fixup_inst (
        .fs_in_target(fs_in),
        .fs_out_target(fixup_out_val)
    );
    assign fs_out = fixup_out_val;
endmodule

module snippet (
    input wire clk,
    input logic inj_fs_in_1755007822820_741,
    input wire reset,
    output wire inj_fs_out_1755007822820_635
);
    mod_fixup_syntax_user mod_fixup_syntax_user_inst_1755007822820_764 (
        .fs_out(inj_fs_out_1755007822820_635),
        .fs_in(inj_fs_in_1755007822820_741)
    );
endmodule

