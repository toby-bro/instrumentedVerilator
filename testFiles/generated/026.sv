module snippet (
    input wire clk,
    input logic [1:0] inj_large_data_in_1755007759108_228,
    input wire reset,
    output logic [7:0] inj_large_sum_out_1755007759108_858
);
    // BEGIN: loop_unroll_limit_test_ts1755007759108
    logic [7:0] current_large_sum_ts1755007759108;
    always_comb begin
        current_large_sum_ts1755007759108 = 8'h00;
        for (int m = 0; m < 40; m = m + 1) begin 
            current_large_sum_ts1755007759108 = current_large_sum_ts1755007759108 + inj_large_data_in_1755007759108_228[0];
            current_large_sum_ts1755007759108 = current_large_sum_ts1755007759108 + inj_large_data_in_1755007759108_228[1];
            current_large_sum_ts1755007759108 = current_large_sum_ts1755007759108 + 1;
        end
        inj_large_sum_out_1755007759108_858 = current_large_sum_ts1755007759108;
    end
    // END: loop_unroll_limit_test_ts1755007759108
endmodule

