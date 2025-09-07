module loop_unroll_limit_test (
    input logic [1:0] large_data_in,
    output logic [7:0] large_sum_out
);
    logic [7:0] current_large_sum;
    always_comb begin
        current_large_sum = 8'h00;
        for (int m = 0; m < 40; m = m + 1) begin 
            current_large_sum = current_large_sum + large_data_in[0];
            current_large_sum = current_large_sum + large_data_in[1];
            current_large_sum = current_large_sum + 1;
        end
        large_sum_out = current_large_sum;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_condition_cc_1755007820538_705,
    input logic [7:0] inj_in1_a_1755007820537_582,
    input logic [1:0] inj_large_data_in_1755007820538_53,
    input logic [7:0] inj_val2_cc_1755007820538_687,
    input logic [7:0] inj_val3_cc_1755007820538_226,
    input wire reset,
    output logic [7:0] inj_large_sum_out_1755007820538_586,
    output logic [7:0] inj_out1_a_1755007820537_784,
    output logic [7:0] inj_out_reg_cc_1755007820538_5
);
    // BEGIN: split_basic_blocking_ts1755007820538
    // BEGIN: split_conditional_reorder_ts1755007820538
    always @(posedge clk) begin
        inj_out_reg_cc_1755007820538_5 <= inj_in1_a_1755007820537_582;
        if (inj_condition_cc_1755007820538_705) begin
            inj_out_reg_cc_1755007820538_5 <= inj_val2_cc_1755007820538_687;
        end else begin
            inj_out_reg_cc_1755007820538_5 <= inj_val3_cc_1755007820538_226;
        end
    end
    // END: split_conditional_reorder_ts1755007820538

    loop_unroll_limit_test loop_unroll_limit_test_inst_1755007820538_9819 (
        .large_data_in(inj_large_data_in_1755007820538_53),
        .large_sum_out(inj_large_sum_out_1755007820538_586)
    );
    always @(*) begin
        inj_out1_a_1755007820537_784 = inj_in1_a_1755007820537_582;
    end
    // END: split_basic_blocking_ts1755007820538
endmodule

