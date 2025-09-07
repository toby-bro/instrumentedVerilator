module snippet (
    input wire clk,
    input wire [3:0] inj_data_in_1755007877570_570,
    input wire [1:0] inj_sel_1755007877570_941,
    input wire reset,
    output reg [3:0] inj_case_out_1755007877570_120
);
    // BEGIN: CaseZExample_ts1755007877570
    wire [3:0] local_data_ts1755007877570;
    assign local_data_ts1755007877570 = inj_data_in_1755007877570_570;
    always @* begin
        casez (inj_sel_1755007877570_941)
            2'b0?: inj_case_out_1755007877570_120 = local_data_ts1755007877570;
            2'b10: inj_case_out_1755007877570_120 = 4'b1111;
            default: inj_case_out_1755007877570_120 = 4'b0000;
        endcase
    end
    // END: CaseZExample_ts1755007877570
endmodule

