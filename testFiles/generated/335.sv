module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007866747_903,
    input wire reset,
    output logic [4:0] inj_internal_out_1755007866747_942
);
    // BEGIN: case_full_simple_mod_ts1755007866747
    always @* begin
        (* full *)
        case (inj_case_expr_1755007866747_903)
            2'b00: inj_internal_out_1755007866747_942 = 10;
            2'b01: inj_internal_out_1755007866747_942 = 11;
            2'b10: inj_internal_out_1755007866747_942 = 12;
            default: inj_internal_out_1755007866747_942 = 13;
        endcase
    end
    // END: case_full_simple_mod_ts1755007866747
endmodule

