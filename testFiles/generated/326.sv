module snippet (
    input wire clk,
    input logic [1:0] inj_in_val_1755007863782_313,
    input wire reset,
    output reg inj_out_res_1755007863782_10
);
    // BEGIN: case_single_default_after_item_ts1755007863782
    always_comb begin
        inj_out_res_1755007863782_10 = 1'b0;
        case (inj_in_val_1755007863782_313)
            2'b01: inj_out_res_1755007863782_10 = 1'b1;
            default: inj_out_res_1755007863782_10 = 1'b0;
            2'b10: inj_out_res_1755007863782_10 = 1'b1;
        endcase
    end
    // END: case_single_default_after_item_ts1755007863782
endmodule

