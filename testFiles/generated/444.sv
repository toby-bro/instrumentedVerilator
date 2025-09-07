module snippet (
    input wire clk,
    input logic [1:0] inj_in_val_1755007902616_999,
    input wire reset,
    output reg inj_out_res_1755007902616_726
);
    // BEGIN: case_basic_ts1755007902616
    always_comb begin
        inj_out_res_1755007902616_726 = 1'b0;
        case (inj_in_val_1755007902616_999)
            2'b00: inj_out_res_1755007902616_726 = 1'b0;
            2'b01: inj_out_res_1755007902616_726 = 1'b1;
            2'b10: inj_out_res_1755007902616_726 = 1'b0;
            2'b11: inj_out_res_1755007902616_726 = 1'b1;
        endcase
    end
    // END: case_basic_ts1755007902616
endmodule

