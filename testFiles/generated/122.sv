module snippet (
    input wire clk,
    input logic inj_data_value_1755007793787_568,
    input logic [7:0] inj_in_false_d_1755007793787_302,
    input logic [7:0] inj_in_true_d_1755007793787_720,
    input logic inj_level1_en_1755007793787_393,
    input logic inj_level2_en_1755007793787_729,
    input wire reset,
    output logic [7:0] inj_out_reg_d_1755007793787_471,
    output logic inj_result_out_1755007793787_233
);
    // BEGIN: nested_blocks_ts1755007793787
    // BEGIN: split_conditional_nb_ts1755007793787
    always @(posedge clk) begin
        if (inj_level2_en_1755007793787_729) begin
            inj_out_reg_d_1755007793787_471 <= inj_in_true_d_1755007793787_720;
        end else begin
            inj_out_reg_d_1755007793787_471 <= inj_in_false_d_1755007793787_302;
        end
    end
    // END: split_conditional_nb_ts1755007793787

    always_comb begin : main_block 
        inj_result_out_1755007793787_233 = 1'b0; 
        if (inj_level1_en_1755007793787_393) begin : inner_block1 
            if (inj_level2_en_1755007793787_729) begin : inner_block2 
                inj_result_out_1755007793787_233 = inj_data_value_1755007793787_568;
            end 
        end 
    end
    // END: nested_blocks_ts1755007793787
endmodule

