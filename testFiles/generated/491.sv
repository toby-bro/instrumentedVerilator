module CombinationalLogic (
    input logic enable,
    input logic [3:0] val_a,
    input logic [3:0] val_b,
    output logic [3:0] result
);
    always_comb begin
        if (enable) begin
            result = val_a + val_b;
        end else begin
            result = 4'h0;
        end
    end
endmodule

module sequential_register (
    input logic clk,
    input logic data_in,
    input logic enable_in,
    input logic reset_n,
    output logic data_out
);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            data_out <= 1'b0; 
        end else if (enable_in) begin
            data_out <= data_in; 
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_c1_x_1755007918457_532,
    input logic inj_c2_x_1755007918457_291,
    input logic inj_c3_x_1755007918457_393,
    input logic [7:0] inj_v1_x_1755007918457_681,
    input logic [7:0] inj_v2_x_1755007918457_230,
    input logic [7:0] inj_v3_x_1755007918457_35,
    input logic [7:0] inj_v4_x_1755007918457_446,
    input logic [3:0] inj_val_a_1755007918458_3,
    input logic [3:0] inj_val_b_1755007918458_870,
    input wire reset,
    output logic inj_data_out_1755007918459_163,
    output wire inj_o_1755007918462_530,
    output logic inj_out_i_1755007918460_104,
    output logic [7:0] inj_out_x_1755007918457_46,
    output logic inj_protected_active_1755007918461_347,
    output logic [3:0] inj_result_1755007918458_134
);
    // BEGIN: split_ifelse_chain_ts1755007918457
    // BEGIN: LintAsyncFovIssue_ts1755007918460
    // BEGIN: PragmaProtectBoundaries_ts1755007918461
logic internal_state_ts1755007918461;
    // BEGIN: buf_primitive_ts1755007918462
    buf b1 (inj_o_1755007918462_530, clk);
    // END: buf_primitive_ts1755007918462

`ifdef SLANG_PRAGMA
`protect begin
`endif
assign internal_state_ts1755007918461 = inj_c2_x_1755007918457_291;
`ifdef SLANG_PRAGMA
`protect end
`endif
`ifdef SLANG_PRAGMA
`protect begin_protected
`endif
`ifdef SLANG_PRAGMA
`protect end_protected
`endif
assign inj_protected_active_1755007918461_347 = internal_state_ts1755007918461;
    // END: PragmaProtectBoundaries_ts1755007918461

    always_ff @(posedge clk or negedge reset) begin
        if (!reset) begin
            inj_out_i_1755007918460_104 <= 1'b0;
        end else begin
            inj_out_i_1755007918460_104 <= inj_c2_x_1755007918457_291 & inj_out_i_1755007918460_104;
        end
    end
    // END: LintAsyncFovIssue_ts1755007918460

    sequential_register sequential_register_inst_1755007918459_1537 (
        .data_in(inj_c3_x_1755007918457_393),
        .enable_in(inj_c1_x_1755007918457_532),
        .reset_n(reset),
        .data_out(inj_data_out_1755007918459_163),
        .clk(clk)
    );
    CombinationalLogic CombinationalLogic_inst_1755007918458_3526 (
        .enable(inj_c2_x_1755007918457_291),
        .val_a(inj_val_a_1755007918458_3),
        .val_b(inj_val_b_1755007918458_870),
        .result(inj_result_1755007918458_134)
    );
    always @(posedge clk) begin
        if (inj_c1_x_1755007918457_532) begin
            inj_out_x_1755007918457_46 <= inj_v1_x_1755007918457_681;
        end else if (inj_c2_x_1755007918457_291) begin
            inj_out_x_1755007918457_46 <= inj_v2_x_1755007918457_230;
        end else if (inj_c3_x_1755007918457_393) begin
            inj_out_x_1755007918457_46 <= inj_v3_x_1755007918457_35;
        end else begin
            inj_out_x_1755007918457_46 <= inj_v4_x_1755007918457_446;
        end
    end
    // END: split_ifelse_chain_ts1755007918457
endmodule

