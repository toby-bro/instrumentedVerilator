module snippet (
    input wire clk,
    input logic inj_d_1755004205897_170,
    input logic [1:0] inj_large_data_in_1755004205897_680,
    input wire reset,
    output logic [7:0] inj_large_sum_out_1755004205897_690,
    output logic inj_q_1755004205897_850
);
    // BEGIN: ModClockedResetReg_ts1755004205897
    // BEGIN: loop_unroll_limit_test_ts1755004205898
    logic [7:0] current_large_sum_ts1755004205897;
    always_comb begin
        current_large_sum_ts1755004205897 = 8'h00;
        for (int m = 0; m < 40; m = m + 1) begin 
            current_large_sum_ts1755004205897 = current_large_sum_ts1755004205897 + inj_large_data_in_1755004205897_680[0];
            current_large_sum_ts1755004205897 = current_large_sum_ts1755004205897 + inj_large_data_in_1755004205897_680[1];
            current_large_sum_ts1755004205897 = current_large_sum_ts1755004205897 + 1;
        end
        inj_large_sum_out_1755004205897_690 = current_large_sum_ts1755004205897;
    end
    // END: loop_unroll_limit_test_ts1755004205898

    always @(posedge clk or negedge reset) begin
    if (!reset) begin
        inj_q_1755004205897_850 <= 1'b0;
    end else begin
        inj_q_1755004205897_850 <= inj_d_1755004205897_170;
    end
    end
    // END: ModClockedResetReg_ts1755004205897
endmodule

