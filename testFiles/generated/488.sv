module case_priority_casex_complex_mod (
    input logic [1:0] case_expr,
    input logic [3:0] case_inside_val,
    output logic [4:0] internal_out
);
    always @* begin
        priority casex ({case_expr, case_inside_val[1:0]})
            4'b1???: internal_out = 24;
            4'b?1??: internal_out = 25;  
            4'b??1?: internal_out = 26;  
            4'b???1: internal_out = 27;  
            4'b0000: internal_out = 28;  
            default: internal_out = 29;
        endcase
    end
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007917502_692,
    input logic [3:0] inj_case_inside_val_1755007917502_466,
    input wire reset,
    output logic [4:0] inj_internal_out_1755007917502_327
);
    case_priority_casex_complex_mod case_priority_casex_complex_mod_inst_1755007917502_9137 (
        .case_expr(inj_case_expr_1755007917502_692),
        .case_inside_val(inj_case_inside_val_1755007917502_466),
        .internal_out(inj_internal_out_1755007917502_327)
    );
endmodule

