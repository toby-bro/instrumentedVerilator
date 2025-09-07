module coalesced_assign (
    input logic [3:0] in_h,
    input logic [3:0] in_l,
    output logic [7:0] out
);
    wire [7:0] temp_wire;
    assign temp_wire[7:4] = in_h;
    assign temp_wire[3:0] = in_l;
    assign out = temp_wire;
endmodule

module snippet (
    input wire clk,
    input logic inj_fs_in_target_1755007837446_592,
    input logic [3:0] inj_in_h_1755007837446_294,
    input logic [3:0] inj_in_l_1755007837446_739,
    input wire reset,
    output logic inj_fs_out_target_1755007837446_526,
    output logic [7:0] inj_out_1755007837446_49
);
    // BEGIN: mod_fixup_target_ts1755007837446
    coalesced_assign coalesced_assign_inst_1755007837446_9475 (
        .out(inj_out_1755007837446_49),
        .in_h(inj_in_h_1755007837446_294),
        .in_l(inj_in_l_1755007837446_739)
    );
    assign inj_fs_out_target_1755007837446_526 = inj_fs_in_target_1755007837446_592;
    // END: mod_fixup_target_ts1755007837446
endmodule

