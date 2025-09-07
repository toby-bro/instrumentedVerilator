module constant_sel (
    input logic [31:0] in,
    output logic [7:0] out1,
    output logic out2
);
    assign out1 = in[15:8];
    assign out2 = in[3];
endmodule

module snippet (
    input wire clk,
    input logic inj_fs_in_target_1755004206972_618,
    input logic [31:0] inj_in_1755004206972_261,
    input logic [3:0] inj_start_val_1755004206972_353,
    input wire reset,
    output logic [7:0] inj_final_val_1755004206972_118,
    output logic inj_fs_out_target_1755004206972_458,
    output logic [7:0] inj_out1_1755004206972_204,
    output logic inj_out2_1755004206972_235
);
    // BEGIN: mod_fixup_target_ts1755004206972
    // BEGIN: loop_with_internal_assign_ts1755004206972
    logic [7:0] current_val_ts1755004206972;
        constant_sel constant_sel_inst_1755004206972_5214 (
            .in(inj_in_1755004206972_261),
            .out1(inj_out1_1755004206972_204),
            .out2(inj_out2_1755004206972_235)
        );
    always_comb begin
        current_val_ts1755004206972 = inj_start_val_1755004206972_353;
        for (int k = 0; k < 3; k = k + 1) begin
            current_val_ts1755004206972 = current_val_ts1755004206972 + 1;
        end
        inj_final_val_1755004206972_118 = current_val_ts1755004206972;
    end
    // END: loop_with_internal_assign_ts1755004206972

    assign inj_fs_out_target_1755004206972_458 = inj_fs_in_target_1755004206972_618;
    // END: mod_fixup_target_ts1755004206972
endmodule

