module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007781635_983,
    input wire reset,
    output logic [4:0] inj_internal_out_1755007781635_52
);
    // BEGIN: case_full_simple_mod_ts1755007781635
    always @* begin
        (* full *)
        case (inj_case_expr_1755007781635_983)
            2'b00: inj_internal_out_1755007781635_52 = 10;
            2'b01: inj_internal_out_1755007781635_52 = 11;
            2'b10: inj_internal_out_1755007781635_52 = 12;
            default: inj_internal_out_1755007781635_52 = 13;
        endcase
    end
    // END: case_full_simple_mod_ts1755007781635
endmodule

