module mod_casez_wildcard (
    input bit [3:0] in_mask_z,
    output bit [1:0] out_match_type_z
);
always_comb begin
    casez (in_mask_z)
        4'b10?0: begin
            out_match_type_z = 2'b00;
        end
        4'b011?: begin
            out_match_type_z = 2'b01;
        end
        default: begin
            out_match_type_z = 2'b11;
        end
    endcase
end
endmodule

module module_latch (
    input wire [7:0] in_latch_data,
    input wire in_latch_en,
    output reg [7:0] out_latch_reg
);
    always_latch begin
    if (in_latch_en) begin
        out_latch_reg = in_latch_data;
    end
    end
endmodule

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module split_basic_blocking (
    input wire clk,
    input logic [7:0] in1_a,
    input wire inj_g_in_1755538606281_382,
    input logic [3:0] inj_i_bind_control_1755538606277_926,
    input logic [15:0] inj_in1_1755538606275_882,
    input logic [7:0] inj_in1_1755538606276_851,
    input logic [15:0] inj_in2_1755538606275_72,
    input logic [7:0] inj_in2_1755538606276_235,
    input wire [7:0] inj_in_latch_data_1755538606283_778,
    input bit [3:0] inj_in_mask_z_1755538606275_778,
    input int inj_val_false_1755538606278_123,
    input int inj_val_true_1755538606278_984,
    input wire [31:0] inj_wide_in_1755538606277_854,
    input wire rst,
    output wire inj_g_out_and_1755538606281_74,
    output wire inj_g_out_or_1755538606281_324,
    output wire [7:0] inj_lower_byte_out_1755538606277_87,
    output logic inj_nand_out_1755538606276_568,
    output logic inj_nor_out_1755538606276_687,
    output logic inj_o_bind_status_1755538606277_813,
    output logic [15:0] inj_out1_1755538606275_845,
    output logic inj_out1_1755538606282_961,
    output logic [15:0] inj_out2_1755538606275_875,
    output logic [7:0] inj_out_diff_m2_1755538606279_22,
    output reg [7:0] inj_out_latch_reg_1755538606283_378,
    output bit [1:0] inj_out_match_type_z_1755538606275_320,
    output int inj_out_val_1755538606278_603,
    output int inj_out_val_1755538606278_723,
    output logic inj_out_valid_1755538606275_513,
    output logic [7:0] inj_out_vec_y_1755538606280_876,
    output wire [7:0] inj_upper_byte_out_1755538606277_65,
    output logic [7:0] inj_var_out_m2_1755538606279_321,
    output logic inj_xnor_out_1755538606276_32,
    output logic [7:0] out1_a
);
    // BEGIN: ModuleImplicitPort_ts1755538606275
    logic valid_ts1755538606275;
        // BEGIN: procedural_complex_ts1755538606276
        logic [15:0] temp1_ts1755538606276;
        logic [15:0] temp2_ts1755538606276;
            // BEGIN: part_select_ops_ts1755538606277
            wire [31:0] processed_wide_ts1755538606277;
                // BEGIN: expr_postsub_comb_ts1755538606279
                logic [7:0] var_m2_ts1755538606279;
                    // BEGIN: ModuleLineDirective_ts1755538606282
                    logic internal_sig_a_ts1755538606282;
                    logic internal_sig_b_ts1755538606282;
                    logic unused_line_var_ts1755538606282;
                        module_latch module_latch_inst_1755538606283_429 (
                            .in_latch_data(inj_in_latch_data_1755538606283_778),
                            .in_latch_en(inj_g_in_1755538606281_382),
                            .out_latch_reg(inj_out_latch_reg_1755538606283_378)
                        );
                    `line 100 "virtual_file_A.sv" 1
                    assign internal_sig_a_ts1755538606282 = valid_ts1755538606275;
                    `line 20 "virtual_file_B.sv" 1
                    assign internal_sig_b_ts1755538606282 = ~internal_sig_a_ts1755538606282;
                    assign unused_line_var_ts1755538606282 = 1'b1;
                    `line 150 "virtual_file_A.sv" 2
                    assign inj_out1_1755538606282_961 = internal_sig_b_ts1755538606282;
                    `line 1 "original_file.sv" 0
                    // END: ModuleLineDirective_ts1755538606282

                    // BEGIN: Module_GatePrimitives_ts1755538606281
                    and a1 (inj_g_out_and_1755538606281_74, inj_g_in_1755538606281_382, inj_g_in_1755538606281_382);
                    or  o1 (inj_g_out_or_1755538606281_324 , inj_g_in_1755538606281_382, inj_g_in_1755538606281_382);
                    // END: Module_GatePrimitives_ts1755538606281

                    // BEGIN: split_vector_assign_ts1755538606280
                    always @(posedge clk) begin
                        if (valid_ts1755538606275) begin
                            inj_out_vec_y_1755538606280_876[3:0] <= inj_in1_1755538606276_851[3:0];
                            inj_out_vec_y_1755538606280_876[7:4] <= inj_in1_1755538606276_851[7:4] + 1;
                        end else begin
                            inj_out_vec_y_1755538606280_876 <= 8'hFF;
                        end
                    end
                    // END: split_vector_assign_ts1755538606280

                always_comb begin
                    var_m2_ts1755538606279 = inj_in1_1755538606276_851;
                    inj_out_diff_m2_1755538606279_22 = (var_m2_ts1755538606279--) - inj_in2_1755538606276_235;
                    inj_var_out_m2_1755538606279_321 = var_m2_ts1755538606279;
                end
                // END: expr_postsub_comb_ts1755538606279

                // BEGIN: system_names_mod_ts1755538606278
                assign inj_out_val_1755538606278_723 = $bits(inj_val_false_1755538606278_123);
                // END: system_names_mod_ts1755538606278

                // BEGIN: ConditionalOps_ts1755538606278
                assign inj_out_val_1755538606278_603 = valid_ts1755538606275 ? inj_val_true_1755538606278_984 : inj_val_false_1755538606278_123;
                // END: ConditionalOps_ts1755538606278

            assign processed_wide_ts1755538606277 = inj_wide_in_1755538606277_854 * 2;
            assign inj_upper_byte_out_1755538606277_65 = processed_wide_ts1755538606277[31:24];
            assign inj_lower_byte_out_1755538606277_87 = processed_wide_ts1755538606277[7:0];
            // END: part_select_ops_ts1755538606277

            module_to_bind module_to_bind_inst_1755538606277_422 (
                .o_bind_status(inj_o_bind_status_1755538606277_813),
                .i_bind_clk(clk),
                .i_bind_control(inj_i_bind_control_1755538606277_926)
            );
            // BEGIN: remaining_reduction_ops_ts1755538606276
            assign inj_nand_out_1755538606276_568 = ~&inj_in1_1755538606276_851;
            assign inj_nor_out_1755538606276_687 = ~|inj_in2_1755538606276_235;
            assign inj_xnor_out_1755538606276_32 = ^~in1_a;
            // END: remaining_reduction_ops_ts1755538606276

        always_comb begin
            temp1_ts1755538606276 = (inj_in1_1755538606275_882 + inj_in2_1755538606275_72) * 10;
            if (valid_ts1755538606275) begin
                temp2_ts1755538606276 = temp1_ts1755538606276 ^ (inj_in1_1755538606275_882 >>> 2);
                inj_out1_1755538606275_845 = temp2_ts1755538606276 & inj_in2_1755538606275_72;
            end else begin
                temp2_ts1755538606276 = temp1_ts1755538606276 | (inj_in2_1755538606275_72 <<< 3);
                inj_out1_1755538606275_845 = temp2_ts1755538606276 + inj_in1_1755538606275_882;
            end
            inj_out2_1755538606275_875 = temp1_ts1755538606276 - temp2_ts1755538606276;
        end
        // END: procedural_complex_ts1755538606276

    assign valid_ts1755538606275 = |in1_a;
    assign inj_out_valid_1755538606275_513 = valid_ts1755538606275;
    // END: ModuleImplicitPort_ts1755538606275

    mod_casez_wildcard mod_casez_wildcard_inst_1755538606275_3047 (
        .in_mask_z(inj_in_mask_z_1755538606275_778),
        .out_match_type_z(inj_out_match_type_z_1755538606275_320)
    );
    always @(*) begin
        out1_a = in1_a;
    end
endmodule

