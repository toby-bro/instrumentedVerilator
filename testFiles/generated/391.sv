module CombinationalLogicExplicit (
    input logic [15:0] data0,
    input logic [15:0] data1,
    input logic sel,
    output logic [15:0] data_out
);
    always @(sel or data0 or data1) begin
        if (sel) begin
            data_out = data1;
        end else begin
            data_out = data0;
        end
    end
endmodule

module basic_assign_if (
    input logic in_a,
    input logic in_b,
    output logic out_c
);
    logic intermediate_wire;
    assign intermediate_wire = in_a & in_b;
    always_comb begin
        if (intermediate_wire) begin
            out_c = 1'b1;
        end else begin
            out_c = 1'b0;
        end
    end
endmodule

module case_full_parallel_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        (* full, parallel *)
        case (case_expr)
            2'b00: internal_out = 1;
            2'b01: internal_out = 2;
            2'b10: internal_out = 3;
            default: internal_out = 4;
        endcase
    end
endmodule

module snippet #(
    parameter integer UNUSED_PARAM = 8
) (
    input wire clk,
    input wire [1:0] inj_byte_idx_1755007885276_974,
    input logic [1:0] inj_case_expr_1755007885257_166,
    input logic [15:0] inj_data0_1755007885255_439,
    input logic [15:0] inj_data1_1755007885255_227,
    input wire [7:0] inj_in1_1755007885256_543,
    input wire [7:0] inj_in2_1755007885256_837,
    input logic inj_in_b_1755007885262_379,
    input logic [7:0] inj_in_val_1755007885255_735,
    input logic inj_sel_1755007885255_62,
    input wire [31:0] inj_wide_data_1755007885276_214,
    input wire reset,
    output logic [15:0] inj_data_out_1755007885255_338,
    output logic [7:0] inj_data_out_fmt_1755007885263_991,
    output logic [7:0] inj_data_out_k_1755007885272_152,
    output logic inj_fs_out_target_1755007885270_976,
    output logic [4:0] inj_internal_out_1755007885257_689,
    output logic [4:0] inj_internal_out_1755007885261_912,
    output wire [7:0] inj_out1_1755007885256_927,
    output wire [7:0] inj_out2_1755007885256_624,
    output logic inj_out_c_1755007885262_729,
    output logic inj_out_n_1755007885260_188,
    output logic [7:0] inj_out_reg_p_1755007885256_817,
    output logic [7:0] inj_out_val_1755007885255_599,
    output logic inj_protected_active_1755007885266_557,
    output reg [7:0] inj_selected_byte_1755007885276_493
);
    // BEGIN: ModuleGenerateIf_ts1755007885255
    parameter int PROCESS_ENABLE = 1;
    logic [7:0] processed_val_ts1755007885255;
        // BEGIN: multi_always_comb_ts1755007885256
        logic [7:0] intermediate1_ts1755007885256;
        logic [7:0] intermediate2_ts1755007885256;
            // BEGIN: formatting_stress_ts1755007885264
            logic [7:0] temp_reg_fmt_ts1755007885264; 
            always_comb begin : stress_comb_block_label 
                inj_data_out_fmt_1755007885263_991 = 8'hXX; 
                if (inj_in_b_1755007885262_379) begin
                    if (inj_sel_1755007885255_62) begin
                        case (inj_case_expr_1755007885257_166) 
                            2'b00: inj_data_out_fmt_1755007885263_991 = intermediate2_ts1755007885256;
                            2'b01: begin 
                                inj_data_out_fmt_1755007885263_991 = ~intermediate2_ts1755007885256; 
                                end 
                            2'b10: begin 
                                logic [7:0] added_val_ts1755007885264; 
                                    // BEGIN: PragmaProtectBoundaries_ts1755007885266
                                logic internal_state_ts1755007885266;
                                    // BEGIN: Bit_Manip_ts1755007885276
                                    always_comb begin
                                        case (inj_byte_idx_1755007885276_974)
                                            2'b00: inj_selected_byte_1755007885276_493 = inj_wide_data_1755007885276_214[7:0];
                                            2'b01: inj_selected_byte_1755007885276_493 = inj_wide_data_1755007885276_214[15:8];
                                            2'b10: inj_selected_byte_1755007885276_493 = inj_wide_data_1755007885276_214[23:16];
                                            default: inj_selected_byte_1755007885276_493 = inj_wide_data_1755007885276_214[31:24];
                                        endcase
                                    end
                                    // END: Bit_Manip_ts1755007885276

                                    // BEGIN: split_input_only_var_ts1755007885272
                                    always @(posedge clk) begin
                                        if (inj_sel_1755007885255_62) begin
                                            inj_data_out_k_1755007885272_152 <= added_val_ts1755007885264;
                                        end
                                    end
                                    // END: split_input_only_var_ts1755007885272

                                    // BEGIN: mod_fixup_target_ts1755007885270
                                    assign inj_fs_out_target_1755007885270_976 = inj_sel_1755007885255_62;
                                    // END: mod_fixup_target_ts1755007885270

                                `ifdef SLANG_PRAGMA
                                `protect begin
                                `endif
                                assign internal_state_ts1755007885266 = inj_sel_1755007885255_62;
                                `ifdef SLANG_PRAGMA
                                `protect end
                                `endif
                                `ifdef SLANG_PRAGMA
                                `protect begin_protected
                                `endif
                                `ifdef SLANG_PRAGMA
                                `protect end_protected
                                `endif
                                assign inj_protected_active_1755007885266_557 = internal_state_ts1755007885266;
                                    // END: PragmaProtectBoundaries_ts1755007885266

                                added_val_ts1755007885264 = intermediate2_ts1755007885256 + 8'h01; 
                                inj_data_out_fmt_1755007885263_991 = added_val_ts1755007885264; 
                                end 
                            default: inj_data_out_fmt_1755007885263_991 = 8'hFF; 
                        endcase 
                    end else begin
                        inj_data_out_fmt_1755007885263_991 = intermediate2_ts1755007885256 - 8'h01; 
                    end 
                end else begin
                    inj_data_out_fmt_1755007885263_991 = 8'h00; 
                end 
            end
            // END: formatting_stress_ts1755007885264

            basic_assign_if basic_assign_if_inst_1755007885262_0 (
                .in_a(inj_sel_1755007885255_62),
                .in_b(inj_in_b_1755007885262_379),
                .out_c(inj_out_c_1755007885262_729)
            );
            case_full_parallel_mod case_full_parallel_mod_inst_1755007885261_3672 (
                .internal_out(inj_internal_out_1755007885261_912),
                .case_expr(inj_case_expr_1755007885257_166)
            );
            // BEGIN: LintParamUnused_ts1755007885260
            assign inj_out_n_1755007885260_188 = inj_sel_1755007885255_62;
            // END: LintParamUnused_ts1755007885260

            // BEGIN: case_full_parallel_mod_ts1755007885258
            always @* begin
                (* full, parallel *)
                case (inj_case_expr_1755007885257_166)
                    2'b00: inj_internal_out_1755007885257_689 = 1;
                    2'b01: inj_internal_out_1755007885257_689 = 2;
                    2'b10: inj_internal_out_1755007885257_689 = 3;
                    default: inj_internal_out_1755007885257_689 = 4;
                endcase
            end
            // END: case_full_parallel_mod_ts1755007885258

            // BEGIN: split_if_empty_then_ts1755007885257
            always @(posedge clk) begin
                if (inj_sel_1755007885255_62) begin
                end else begin
                    inj_out_reg_p_1755007885256_817 <= intermediate1_ts1755007885256;
                end
            end
            // END: split_if_empty_then_ts1755007885257

        always @(*) begin
            intermediate1_ts1755007885256 = inj_in1_1755007885256_543 & inj_in2_1755007885256_837;
        end
        always @(*) begin
            intermediate2_ts1755007885256 = inj_in1_1755007885256_543 | inj_in2_1755007885256_837;
        end
        assign inj_out1_1755007885256_927 = intermediate1_ts1755007885256 + 8'd1;
        assign inj_out2_1755007885256_624 = intermediate2_ts1755007885256 - 8'd1;
        // END: multi_always_comb_ts1755007885256

    generate
        if (PROCESS_ENABLE) begin : process_block
            assign processed_val_ts1755007885255 = inj_in_val_1755007885255_735 + 10;
        end else begin : bypass_block
            assign processed_val_ts1755007885255 = inj_in_val_1755007885255_735;
        end
    endgenerate
    assign inj_out_val_1755007885255_599 = processed_val_ts1755007885255;
    // END: ModuleGenerateIf_ts1755007885255

    CombinationalLogicExplicit CombinationalLogicExplicit_inst_1755007885255_2545 (
        .data_out(inj_data_out_1755007885255_338),
        .data0(inj_data0_1755007885255_439),
        .data1(inj_data1_1755007885255_227),
        .sel(inj_sel_1755007885255_62)
    );
endmodule

