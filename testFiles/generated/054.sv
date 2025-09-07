module case_priority_overlapping_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        priority casez (case_expr)
            2'b1?: internal_out = 5;
            2'b?1: internal_out = 6;  
            2'b0?: internal_out = 7;
            2'b?0: internal_out = 8;  
            default: internal_out = 9;
        endcase
    end
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007769635_426,
    input logic [7:0] inj_i_target_data_1755007769634_239,
    input wire reset,
    output logic [4:0] inj_internal_out_1755007769635_532,
    output logic [7:0] inj_o_target_result_1755007769634_165
);
    // BEGIN: target_module_for_bind_ts1755007769634
    case_priority_overlapping_mod case_priority_overlapping_mod_inst_1755007769635_4267 (
        .case_expr(inj_case_expr_1755007769635_426),
        .internal_out(inj_internal_out_1755007769635_532)
    );
    always_comb inj_o_target_result_1755007769634_165 = inj_i_target_data_1755007769634_239 + 1;
    // END: target_module_for_bind_ts1755007769634
endmodule

