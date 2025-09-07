module snippet (
    input wire clk,
    input logic inj_condition_z_1755007892019_783,
    input logic [7:0] inj_in1_z_1755007892019_484,
    input logic [7:0] inj_in2_z_1755007892019_129,
    input int inj_in_val_1755007892018_159,
    input wire reset,
    output logic [7:0] inj_out1_z_1755007892019_788,
    output logic [7:0] inj_out2_z_1755007892019_42,
    output int inj_out_val_1755007892018_107
);
    // BEGIN: definition_used_diag_mod_ts1755007892018
    // BEGIN: split_diff_vars_branches_ts1755007892019
    always @(posedge clk) begin
        if (inj_condition_z_1755007892019_783) begin
            inj_out1_z_1755007892019_788 <= inj_in1_z_1755007892019_484;
        end else begin
            inj_out2_z_1755007892019_42 <= inj_in2_z_1755007892019_129;
        end
    end
    // END: split_diff_vars_branches_ts1755007892019

    assign inj_out_val_1755007892018_107 = inj_in_val_1755007892018_159;
    // END: definition_used_diag_mod_ts1755007892018
endmodule

