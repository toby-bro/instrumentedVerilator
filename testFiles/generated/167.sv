module snippet (
    input wire clk,
    input logic inj_data_value_1755007809077_929,
    input logic inj_level1_en_1755007809077_223,
    input logic inj_level2_en_1755007809077_874,
    input wire reset,
    output logic inj_result_out_1755007809077_368
);
    // BEGIN: nested_blocks_ts1755007809077
    always_comb begin : main_block 
        inj_result_out_1755007809077_368 = 1'b0; 
        if (inj_level1_en_1755007809077_223) begin : inner_block1 
            if (inj_level2_en_1755007809077_874) begin : inner_block2 
                inj_result_out_1755007809077_368 = inj_data_value_1755007809077_929;
            end 
        end 
    end
    // END: nested_blocks_ts1755007809077
endmodule

