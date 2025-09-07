module snippet (
    input wire clk,
    input logic [7:0] inj_in_val_a_l_1755007919687_378,
    input logic [7:0] inj_in_val_b_l_1755007919687_433,
    input wire reset,
    output logic [8:0] inj_out_val_c_l_1755007919687_417,
    output logic [7:0] inj_out_val_d_l_1755007919687_97
);
    // BEGIN: split_inputs_outputs_only_ts1755007919687
    always @(*) begin
        inj_out_val_c_l_1755007919687_417 = inj_in_val_a_l_1755007919687_378 + inj_in_val_b_l_1755007919687_433;
        inj_out_val_d_l_1755007919687_97 = inj_in_val_a_l_1755007919687_378 - inj_in_val_b_l_1755007919687_433;
    end
    // END: split_inputs_outputs_only_ts1755007919687
endmodule

