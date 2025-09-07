module snippet (
    input wire clk,
    input logic [1:0] inj_in_val_1755007908311_18,
    input wire reset,
    output reg inj_out_res_1755007908311_513
);
    // BEGIN: case_empty_statement_ts1755007908311
    always_comb begin
        inj_out_res_1755007908311_513 = 1'b0;
        case (inj_in_val_1755007908311_18)
            2'b00: inj_out_res_1755007908311_513 = 1'b1;
            2'b01: ;
            2'b10: inj_out_res_1755007908311_513 = 1'b0;
            default: inj_out_res_1755007908311_513 = 1'b1;
        endcase
    end
    // END: case_empty_statement_ts1755007908311
endmodule

