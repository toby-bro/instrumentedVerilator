module CombinationalLogicImplicit (
    input logic [3:0] a,
    input logic [3:0] b,
    output logic [3:0] sum
);
    always @* begin
        sum = a + b;
    end
endmodule

module PragmaProtectBoundaries (
    input logic start_protect,
    output logic protected_active
);
logic internal_state;
`ifdef SLANG_PRAGMA
`protect begin
`endif
assign internal_state = start_protect;
`ifdef SLANG_PRAGMA
`protect end
`endif
`ifdef SLANG_PRAGMA
`protect begin_protected
`endif
`ifdef SLANG_PRAGMA
`protect end_protected
`endif
assign protected_active = internal_state;
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_a_1755007795194_693,
    input logic [3:0] inj_b_1755007795194_379,
    input logic [1:0] inj_case_expr_1755007795193_642,
    input logic [7:0] inj_in_a_g_1755007795194_690,
    input logic [7:0] inj_in_b_g_1755007795194_497,
    input logic inj_start_protect_1755007795195_201,
    input wire reset,
    output logic [4:0] inj_internal_out_1755007795193_217,
    output logic inj_out_1755007795195_870,
    output logic [7:0] inj_out_p_g_1755007795194_64,
    output logic [7:0] inj_out_q_g_1755007795194_613,
    output reg inj_out_res_1755007795193_3,
    output logic inj_protected_active_1755007795195_860,
    output logic [3:0] inj_sum_1755007795194_62
);
    // BEGIN: case_priority_overlapping_mod_ts1755007795193
    // BEGIN: case_default_ts1755007795193
    // BEGIN: split_reorder_blocking_ts1755007795194
    logic [7:0] mid_x_g_ts1755007795194;
    logic [7:0] mid_y_g_ts1755007795194;
        PragmaProtectBoundaries PragmaProtectBoundaries_inst_1755007795195_4307 (
            .start_protect(inj_start_protect_1755007795195_201),
            .protected_active(inj_protected_active_1755007795195_860)
        );
        // BEGIN: reduction_ops_ts1755007795195
        assign inj_out_1755007795195_870 = &inj_in_b_g_1755007795194_497 | ^mid_y_g_ts1755007795194;
        // END: reduction_ops_ts1755007795195

        CombinationalLogicImplicit CombinationalLogicImplicit_inst_1755007795194_3133 (
            .a(inj_a_1755007795194_693),
            .b(inj_b_1755007795194_379),
            .sum(inj_sum_1755007795194_62)
        );
    always @(*) begin
        mid_x_g_ts1755007795194 = inj_in_a_g_1755007795194_690 * 2;
        mid_y_g_ts1755007795194 = mid_x_g_ts1755007795194 + inj_in_b_g_1755007795194_497;
        inj_out_p_g_1755007795194_64 = mid_y_g_ts1755007795194 - 1;
        inj_out_q_g_1755007795194_613 = mid_x_g_ts1755007795194 / 2;
    end
    // END: split_reorder_blocking_ts1755007795194

    always_comb begin
        inj_out_res_1755007795193_3 = 1'b0;
        case (inj_case_expr_1755007795193_642)
            2'b01: inj_out_res_1755007795193_3 = 1'b1;
            2'b10: inj_out_res_1755007795193_3 = 1'b0;
            default: inj_out_res_1755007795193_3 = 1'b1;
        endcase
    end
    // END: case_default_ts1755007795193

    always @* begin
        priority casez (inj_case_expr_1755007795193_642)
            2'b1?: inj_internal_out_1755007795193_217 = 5;
            2'b?1: inj_internal_out_1755007795193_217 = 6;  
            2'b0?: inj_internal_out_1755007795193_217 = 7;
            2'b?0: inj_internal_out_1755007795193_217 = 8;  
            default: inj_internal_out_1755007795193_217 = 9;
        endcase
    end
    // END: case_priority_overlapping_mod_ts1755007795193
endmodule

