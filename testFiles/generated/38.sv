module snippet (
    input wire clk,
    input logic [3:0] inj_in_h_1755004216036_959,
    input logic [3:0] inj_in_l_1755004216036_841,
    input logic [1:0] inj_large_data_in_1755004216037_839,
    input wire reset,
    output logic [7:0] inj_large_sum_out_1755004216037_444,
    output logic [3:0] inj_out_1755004216037_43,
    output logic [7:0] inj_out_c_1755004216036_427
);
    // BEGIN: concat_op_ts1755004216037
    // BEGIN: loop_unroll_limit_test_ts1755004216037
    logic [7:0] current_large_sum_ts1755004216037;
        // BEGIN: mismatched_width_unhandled_ts1755004216037
        assign inj_out_1755004216037_43 = current_large_sum_ts1755004216037;
        // END: mismatched_width_unhandled_ts1755004216037

    always_comb begin
        current_large_sum_ts1755004216037 = 8'h00;
        for (int m = 0; m < 40; m = m + 1) begin 
            current_large_sum_ts1755004216037 = current_large_sum_ts1755004216037 + inj_large_data_in_1755004216037_839[0];
            current_large_sum_ts1755004216037 = current_large_sum_ts1755004216037 + inj_large_data_in_1755004216037_839[1];
            current_large_sum_ts1755004216037 = current_large_sum_ts1755004216037 + 1;
        end
        inj_large_sum_out_1755004216037_444 = current_large_sum_ts1755004216037;
    end
    // END: loop_unroll_limit_test_ts1755004216037

    assign inj_out_c_1755004216036_427 = {inj_in_h_1755004216036_959, inj_in_l_1755004216036_841};
    // END: concat_op_ts1755004216037
endmodule

