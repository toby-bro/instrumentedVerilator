module ModSimpleLogic (
    input logic a,
    input logic b,
    output logic y
);
    assign y = a ^ b;
endmodule

module another_module_config_dummy (
    input logic i,
    output logic o
);
    assign o = i & i; 
endmodule

module snippet (
    input wire clk,
    input logic inj_b_1755007750053_923,
    input logic inj_unused_in_1755007750053_832,
    input wire reset,
    output logic inj_o_1755007750053_28,
    output logic inj_unused_out_1755007750053_248,
    output logic inj_y_1755007750053_117
);
    // BEGIN: unreferenced_module_ts1755007750053
    another_module_config_dummy another_module_config_dummy_inst_1755007750053_6200 (
        .o(inj_o_1755007750053_28),
        .i(inj_unused_in_1755007750053_832)
    );
    ModSimpleLogic ModSimpleLogic_inst_1755007750053_716 (
        .a(inj_unused_in_1755007750053_832),
        .b(inj_b_1755007750053_923),
        .y(inj_y_1755007750053_117)
    );
    assign inj_unused_out_1755007750053_248 = ~inj_unused_in_1755007750053_832;
    // END: unreferenced_module_ts1755007750053
endmodule

