module snippet (
    input wire clk,
    input logic [7:0] inj_i_target_data_1755004202743_591,
    input wire reset,
    output logic [7:0] inj_o_target_result_1755004202743_744
);
    // BEGIN: target_module_for_bind_ts1755004202743
    always_comb inj_o_target_result_1755004202743_744 = inj_i_target_data_1755004202743_591 + 1;
    // END: target_module_for_bind_ts1755004202743
endmodule

