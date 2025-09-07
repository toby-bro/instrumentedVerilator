module PragmaResetDirectives (
    input bit reset_request,
    output bit system_status_clear
);
`ifdef SLANG_PRAGMA
`reset protect diagnostic
`endif
assign system_status_clear = reset_request;
endmodule

module case_full_simple_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        (* full *)
        case (case_expr)
            2'b00: internal_out = 10;
            2'b01: internal_out = 11;
            2'b10: internal_out = 12;
            default: internal_out = 13;
        endcase
    end
endmodule

module split_multi_nb_in_if (
    input logic clk_dd,
    input logic cond_dd,
    input logic [7:0] in1_dd,
    input logic [7:0] in2_dd,
    input logic [7:0] in3_dd,
    input logic [7:0] in4_dd,
    output logic [7:0] out1_dd,
    output logic [7:0] out2_dd
);
    always @(posedge clk_dd) begin
        if (cond_dd) begin
            out1_dd <= in1_dd + in2_dd;
            out2_dd <= in3_dd - in4_dd;
        end else begin
            out1_dd <= in1_dd * in2_dd;
            out2_dd <= in3_dd / (in4_dd + 1);
        end
    end
endmodule

module snippet (
    input wire clk,
    input wire [3:0] inj_data_c_1755007840003_608,
    input logic inj_fs_in_target_1755007840004_590,
    input logic [7:0] inj_in1_dd_1755007840005_785,
    input logic [7:0] inj_in2_dd_1755007840005_734,
    input logic [7:0] inj_in3_dd_1755007840005_506,
    input logic [7:0] inj_in4_dd_1755007840005_103,
    input wire [7:0] inj_in_latch_data_1755007840004_567,
    input logic [1:0] inj_in_val_1755007840004_980,
    input wire [1:0] inj_selector_1755007840003_998,
    input wire reset,
    output logic inj_fs_out_target_1755007840004_670,
    output logic [4:0] inj_internal_out_1755007840005_846,
    output logic [7:0] inj_out1_dd_1755007840005_596,
    output logic [7:0] inj_out2_dd_1755007840005_95,
    output logic [3:0] inj_out_case_case_1755007840003_642,
    output logic [3:0] inj_out_case_casex_1755007840003_509,
    output logic [3:0] inj_out_case_casez_1755007840003_103,
    output reg [7:0] inj_out_latch_reg_1755007840004_811,
    output reg inj_out_res_1755007840004_86,
    output bit inj_system_status_clear_1755007840005_557
);
    // BEGIN: CaseStatementConditions_ts1755007840004
    // BEGIN: case_single_default_after_item_ts1755007840004
    // BEGIN: module_latch_ts1755007840004
    // BEGIN: mod_fixup_target_ts1755007840004
    split_multi_nb_in_if split_multi_nb_in_if_inst_1755007840005_1940 (
        .in2_dd(inj_in2_dd_1755007840005_734),
        .in3_dd(inj_in3_dd_1755007840005_506),
        .in4_dd(inj_in4_dd_1755007840005_103),
        .out1_dd(inj_out1_dd_1755007840005_596),
        .out2_dd(inj_out2_dd_1755007840005_95),
        .clk_dd(clk),
        .cond_dd(inj_fs_in_target_1755007840004_590),
        .in1_dd(inj_in1_dd_1755007840005_785)
    );
    PragmaResetDirectives PragmaResetDirectives_inst_1755007840005_88 (
        .reset_request(reset),
        .system_status_clear(inj_system_status_clear_1755007840005_557)
    );
    case_full_simple_mod case_full_simple_mod_inst_1755007840005_1840 (
        .internal_out(inj_internal_out_1755007840005_846),
        .case_expr(inj_in_val_1755007840004_980)
    );
    assign inj_fs_out_target_1755007840004_670 = inj_fs_in_target_1755007840004_590;
    // END: mod_fixup_target_ts1755007840004

    always_latch begin
    if (clk) begin
        inj_out_latch_reg_1755007840004_811 = inj_in_latch_data_1755007840004_567;
    end
    end
    // END: module_latch_ts1755007840004

    always_comb begin
        inj_out_res_1755007840004_86 = 1'b0;
        case (inj_in_val_1755007840004_980)
            2'b01: inj_out_res_1755007840004_86 = 1'b1;
            default: inj_out_res_1755007840004_86 = 1'b0;
            2'b10: inj_out_res_1755007840004_86 = 1'b1;
        endcase
    end
    // END: case_single_default_after_item_ts1755007840004

    always_comb begin
        case (inj_selector_1755007840003_998)
            2'b00: inj_out_case_case_1755007840003_642 = inj_data_c_1755007840003_608;
            2'b01: inj_out_case_case_1755007840003_642 = inj_data_c_1755007840003_608 + 1;
            2'b10: inj_out_case_case_1755007840003_642 = inj_data_c_1755007840003_608 + 2;
            default: inj_out_case_case_1755007840003_642 = 4'bxxxx;
        endcase
        casez (inj_selector_1755007840003_998)
            2'b0?: inj_out_case_casez_1755007840003_103 = inj_data_c_1755007840003_608 + 10;
            2'b1?: inj_out_case_casez_1755007840003_103 = inj_data_c_1755007840003_608 + 20;
            default: inj_out_case_casez_1755007840003_103 = 4'bzzzz;
        endcase
        casex (inj_selector_1755007840003_998)
            2'b0?: inj_out_case_casex_1755007840003_509 = inj_data_c_1755007840003_608 - 1;
            2'b1?: inj_out_case_casex_1755007840003_509 = inj_data_c_1755007840003_608 - 2;
            default: inj_out_case_casex_1755007840003_509 = 4'bxxxx;
        endcase
    end
    // END: CaseStatementConditions_ts1755007840004
endmodule

