module snippet (
    input wire clk,
    input logic inj_in_j_1755007887944_426,
    input logic inj_in_k_1755007887944_275,
    input wire reset,
    output logic inj_out_l_1755007887944_899
);
    // BEGIN: LintLatch_ts1755007887945
    always_comb begin
        if (inj_in_j_1755007887944_426) begin
            inj_out_l_1755007887944_899 = inj_in_k_1755007887944_275;
        end else begin
            inj_out_l_1755007887944_899 = 1'b0; 
        end
    end
    // END: LintLatch_ts1755007887945
endmodule

