module snippet (
    input wire clk,
    input logic [7:0] inj_data_1755007909340_687,
    input logic inj_in_j_1755007909339_669,
    input logic inj_in_k_1755007909339_768,
    input logic [1:0] inj_in_val_1755007909340_54,
    input logic [2:0] inj_shift_val_1755007909340_630,
    input wire reset,
    output logic [7:0] inj_left_shift_log_1755007909340_486,
    output logic inj_out_l_1755007909339_666,
    output reg inj_out_res_1755007909340_891,
    output logic [7:0] inj_right_shift_arith_1755007909340_499,
    output logic [7:0] inj_right_shift_log_1755007909340_689
);
    // BEGIN: LintLatch_ts1755007909339
    // BEGIN: ShiftOperations_ts1755007909340
    // BEGIN: case_single_default_after_item_ts1755007909340
    always_comb begin
        inj_out_res_1755007909340_891 = 1'b0;
        case (inj_in_val_1755007909340_54)
            2'b01: inj_out_res_1755007909340_891 = 1'b1;
            default: inj_out_res_1755007909340_891 = 1'b0;
            2'b10: inj_out_res_1755007909340_891 = 1'b1;
        endcase
    end
    // END: case_single_default_after_item_ts1755007909340

    assign inj_left_shift_log_1755007909340_486 = inj_data_1755007909340_687 << inj_shift_val_1755007909340_630;
    assign inj_right_shift_log_1755007909340_689 = inj_data_1755007909340_687 >> inj_shift_val_1755007909340_630;
    assign inj_right_shift_arith_1755007909340_499 = $signed(inj_data_1755007909340_687) >>> inj_shift_val_1755007909340_630;
    // END: ShiftOperations_ts1755007909340

    always_comb begin
        if (inj_in_j_1755007909339_669) begin
            inj_out_l_1755007909339_666 = inj_in_k_1755007909339_768;
        end else begin
            inj_out_l_1755007909339_666 = 1'b0; 
        end
    end
    // END: LintLatch_ts1755007909339
endmodule

