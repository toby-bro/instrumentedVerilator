module snippet (
    input wire clk,
    input logic inj_c1_x_1755007884640_950,
    input logic inj_c2_x_1755007884640_642,
    input logic inj_c3_x_1755007884640_635,
    input logic [7:0] inj_v1_x_1755007884640_320,
    input logic [7:0] inj_v2_x_1755007884640_81,
    input logic [7:0] inj_v3_x_1755007884640_526,
    input logic [7:0] inj_v4_x_1755007884640_101,
    input wire reset,
    output logic [7:0] inj_out_x_1755007884640_405
);
    // BEGIN: split_ifelse_chain_ts1755007884641
    always @(posedge clk) begin
        if (inj_c1_x_1755007884640_950) begin
            inj_out_x_1755007884640_405 <= inj_v1_x_1755007884640_320;
        end else if (inj_c2_x_1755007884640_642) begin
            inj_out_x_1755007884640_405 <= inj_v2_x_1755007884640_81;
        end else if (inj_c3_x_1755007884640_635) begin
            inj_out_x_1755007884640_405 <= inj_v3_x_1755007884640_526;
        end else begin
            inj_out_x_1755007884640_405 <= inj_v4_x_1755007884640_101;
        end
    end
    // END: split_ifelse_chain_ts1755007884641
endmodule

