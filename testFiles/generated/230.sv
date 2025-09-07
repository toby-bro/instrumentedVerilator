module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007831106_116,
    input logic inj_cond_in_1755007831106_326,
    input wire reset,
    output logic inj_cond_out_1755007831106_366,
    output logic [4:0] inj_internal_out_1755007831106_726
);
    // BEGIN: case_full_parallel_mod_ts1755007831106
    // BEGIN: mod_logical_not_ts1755007831107
    always_comb begin
        inj_cond_out_1755007831106_366 = !inj_cond_in_1755007831106_326;
    end
    // END: mod_logical_not_ts1755007831107

    always @* begin
        (* full, parallel *)
        case (inj_case_expr_1755007831106_116)
            2'b00: inj_internal_out_1755007831106_726 = 1;
            2'b01: inj_internal_out_1755007831106_726 = 2;
            2'b10: inj_internal_out_1755007831106_726 = 3;
            default: inj_internal_out_1755007831106_726 = 4;
        endcase
    end
    // END: case_full_parallel_mod_ts1755007831106
endmodule

