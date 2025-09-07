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

module mod_case_block_attrs (
    input wire [1:0] i_sel,
    input wire [3:0] i_val,
    output logic [3:0] o_out
);
    logic [3:0] l_temp;
    always_comb begin
        (* full_case *)
        (* parallel_case *)
        case (i_sel)
            2'b00: l_temp = i_val;
            2'b01: l_temp = i_val << 1;
            2'b10: l_temp = i_val >> 1;
            default: l_temp = 4'bxxxx;
        endcase
        (* coverage_off *)
        begin : my_named_block
            o_out = l_temp;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_a_1755007899945_371,
    input logic [7:0] inj_b_1755007899945_375,
    input logic [7:0] inj_c_1755007899945_566,
    input logic [1:0] inj_case_expr_1755007899945_128,
    input wire [1:0] inj_i_sel_1755007899945_451,
    input wire [3:0] inj_i_val_1755007899945_874,
    input wire reset,
    output logic inj_anded_1755007899945_968,
    output logic inj_diff_1755007899945_456,
    output logic [4:0] inj_internal_out_1755007899945_214,
    output logic [3:0] inj_o_out_1755007899945_252,
    output logic inj_ored_1755007899945_455,
    output logic [7:0] inj_sum_1755007899945_65,
    output logic inj_xored_1755007899945_889
);
    // BEGIN: more_ops_ts1755007899946
    assign inj_sum_1755007899945_65 = inj_a_1755007899945_371 + inj_b_1755007899945_375;
    assign inj_diff_1755007899945_456 = inj_a_1755007899945_371 > inj_c_1755007899945_566;
    assign inj_anded_1755007899945_968 = inj_a_1755007899945_371 & inj_b_1755007899945_375;
    assign inj_ored_1755007899945_455 = inj_a_1755007899945_371 | inj_c_1755007899945_566;
    assign inj_xored_1755007899945_889 = inj_a_1755007899945_371 ^ inj_b_1755007899945_375;
    // END: more_ops_ts1755007899946

    mod_case_block_attrs mod_case_block_attrs_inst_1755007899945_5700 (
        .i_sel(inj_i_sel_1755007899945_451),
        .i_val(inj_i_val_1755007899945_874),
        .o_out(inj_o_out_1755007899945_252)
    );
    case_priority_overlapping_mod case_priority_overlapping_mod_inst_1755007899945_1205 (
        .case_expr(inj_case_expr_1755007899945_128),
        .internal_out(inj_internal_out_1755007899945_214)
    );
endmodule

