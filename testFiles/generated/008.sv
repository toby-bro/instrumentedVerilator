module mod_fixup_target (
    input logic fs_in_target,
    output logic fs_out_target
);
    assign fs_out_target = fs_in_target;
endmodule

module snippet (
    input wire clk,
    input logic inj_control_signal_k_1755007752875_144,
    input logic [7:0] inj_data_in_k_1755007752875_748,
    input wire reset,
    output logic [7:0] inj_data_out_k_1755007752875_506,
    output logic inj_fs_out_target_1755007752876_776,
    output wire inj_loop_out_1755007752876_148
);
    // BEGIN: split_input_only_var_ts1755007752875
    // BEGIN: Comb_Loop_ts1755007752876
    wire loop_wire1_ts1755007752876;
    wire loop_wire2_ts1755007752876;
        mod_fixup_target mod_fixup_target_inst_1755007752876_717 (
            .fs_out_target(inj_fs_out_target_1755007752876_776),
            .fs_in_target(inj_control_signal_k_1755007752875_144)
        );
    assign loop_wire1_ts1755007752876 = loop_wire2_ts1755007752876 | clk;
    assign loop_wire2_ts1755007752876 = loop_wire1_ts1755007752876; 
    assign inj_loop_out_1755007752876_148 = loop_wire1_ts1755007752876;
    // END: Comb_Loop_ts1755007752876

    always @(posedge clk) begin
        if (inj_control_signal_k_1755007752875_144) begin
            inj_data_out_k_1755007752875_506 <= inj_data_in_k_1755007752875_748;
        end
    end
    // END: split_input_only_var_ts1755007752875
endmodule

