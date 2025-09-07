module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007878394_177,
    input logic [3:0] inj_case_inside_val_1755007878394_612,
    input wire reset,
    output logic [4:0] inj_internal_out_1755007878394_623
);
    // BEGIN: case_priority_casex_complex_mod_ts1755007878394
    always @* begin
        priority casex ({inj_case_expr_1755007878394_177, inj_case_inside_val_1755007878394_612[1:0]})
            4'b1???: inj_internal_out_1755007878394_623 = 24;
            4'b?1??: inj_internal_out_1755007878394_623 = 25;  
            4'b??1?: inj_internal_out_1755007878394_623 = 26;  
            4'b???1: inj_internal_out_1755007878394_623 = 27;  
            4'b0000: inj_internal_out_1755007878394_623 = 28;  
            default: inj_internal_out_1755007878394_623 = 29;
        endcase
    end
    // END: case_priority_casex_complex_mod_ts1755007878394
endmodule

