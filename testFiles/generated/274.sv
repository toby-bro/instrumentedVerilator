module snippet (
    input wire clk,
    input logic inj_condition_z_1755007846185_674,
    input logic [7:0] inj_in1_z_1755007846185_338,
    input logic [7:0] inj_in2_z_1755007846185_560,
    input wire reset,
    output logic [7:0] inj_out1_z_1755007846185_760,
    output logic [7:0] inj_out2_z_1755007846185_382
);
    // BEGIN: split_diff_vars_branches_ts1755007846185
    always @(posedge clk) begin
        if (inj_condition_z_1755007846185_674) begin
            inj_out1_z_1755007846185_760 <= inj_in1_z_1755007846185_338;
        end else begin
            inj_out2_z_1755007846185_382 <= inj_in2_z_1755007846185_560;
        end
    end
    // END: split_diff_vars_branches_ts1755007846185
endmodule

