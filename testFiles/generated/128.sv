module snippet (
    input wire clk,
    input logic inj_in_j_1755007795851_716,
    input logic inj_in_k_1755007795851_667,
    input wire reset,
    output logic inj_out_l_1755007795851_515
);
    // BEGIN: LintLatch_ts1755007795851
    always_comb begin
        if (inj_in_j_1755007795851_716) begin
            inj_out_l_1755007795851_515 = inj_in_k_1755007795851_667;
        end else begin
            inj_out_l_1755007795851_515 = 1'b0; 
        end
    end
    // END: LintLatch_ts1755007795851
endmodule

