module LintLatch (
    input logic in_j,
    input logic in_k,
    output logic out_l
);
    always_comb begin
        if (in_j) begin
            out_l = in_k;
        end else begin
            out_l = 1'b0; 
        end
    end
endmodule

module ModMultipleAlways (
    input logic clk_a,
    input logic clk_b,
    input logic din_a,
    input logic din_b,
    input logic rst_n,
    output logic dout_a,
    output logic dout_b
);
    always @(posedge clk_a or negedge rst_n) begin 
    if (!rst_n) begin 
        dout_a <= 1'b0;
    end else begin
        dout_a <= din_a; 
    end
    end
    always @(posedge clk_b) begin 
    dout_b <= din_b; 
    end
endmodule

module snippet (
    input wire clk,
    input bit [3:0] inj_in1_1755007801181_131,
    input bit [3:0] inj_in2_1755007801181_444,
    input wire [7:0] inj_in_array_data_1755007801172_375,
    input logic [3:0] inj_in_h_1755007801167_242,
    input logic inj_in_k_1755007801170_574,
    input logic [3:0] inj_in_l_1755007801167_208,
    input logic [1:0] inj_in_val_1755007801169_808,
    input logic [7:0] inj_in_val_a_l_1755007801167_383,
    input logic [7:0] inj_in_val_b_l_1755007801167_353,
    input logic [2:0] inj_index_1755007801187_974,
    input wire [1:0] inj_select_idx_1755007801172_541,
    input logic inj_unused_in_1755007801169_956,
    input wire reset,
    output logic [3:0] inj_data_out_1755007801179_411,
    output wire inj_dout_1755007801184_740,
    output logic inj_dout_a_1755007801171_32,
    output logic inj_dout_b_1755007801171_899,
    output reg inj_non_ansi_b_1755007801174_225,
    output logic inj_non_ansi_basic_output_1755007801174_406,
    output bit [3:0] inj_out1_1755007801181_3,
    output logic [7:0] inj_out1_z_1755007801189_584,
    output bit [3:0] inj_out2_1755007801181_397,
    output logic [7:0] inj_out2_z_1755007801189_35,
    output logic inj_out_1755007801187_370,
    output logic [7:0] inj_out_c_1755007801167_178,
    output logic [7:0] inj_out_data_1755007801176_810,
    output wire [3:0] inj_out_element_1755007801172_161,
    output logic inj_out_its_1755007801173_390,
    output logic inj_out_l_1755007801170_301,
    output logic [7:0] inj_out_reg_a_1755007801168_543,
    output logic [7:0] inj_out_reg_b_1755007801168_105,
    output reg inj_out_res_1755007801169_382,
    output logic [8:0] inj_out_val_c_l_1755007801167_825,
    output logic [7:0] inj_out_val_d_l_1755007801167_479,
    output logic inj_unused_out_1755007801169_670
);
    // BEGIN: split_inputs_outputs_only_ts1755007801167
    // BEGIN: concat_op_ts1755007801167
    // BEGIN: mod_split_ff_ts1755007801168
    logic [7:0]  split_reg_var_ts1755007801168;
    logic [7:0] other_reg_var_ts1755007801168;
        // BEGIN: unpacked_array_module_ts1755007801172
        logic [3:0] data_array_ts1755007801172 [4];
            // BEGIN: non_ansi_basic_ts1755007801175
            input wire reset_ts1755007801175;
            output reg inj_non_ansi_b_1755007801174_225_ts1755007801175;
            input logic inj_unused_in_1755007801169_956_ts1755007801175;
            output logic inj_non_ansi_basic_output_1755007801174_406_ts1755007801175;
                // BEGIN: ModuleFF_ts1755007801181
                parameter int MAX_COUNT = 10;
                localparam int START_VAL = 5;
                logic [3:0] ff_reg_ts1755007801181;
                integer unused_int_var_ts1755007801181;
                    // BEGIN: ContinuousWire_ts1755007801184
                    wire internal_w_ts1755007801184;
                        // BEGIN: split_diff_vars_branches_ts1755007801190
                        always @(posedge clk) begin
                            if (inj_unused_in_1755007801169_956) begin
                                inj_out1_z_1755007801189_584 <= other_reg_var_ts1755007801168;
                            end else begin
                                inj_out2_z_1755007801189_35 <= inj_in_val_a_l_1755007801167_383;
                            end
                        end
                        // END: split_diff_vars_branches_ts1755007801190

                        // BEGIN: variable_sel_mux_ts1755007801187
                        assign inj_out_1755007801187_370 = inj_in_val_a_l_1755007801167_383[inj_index_1755007801187_974];
                        // END: variable_sel_mux_ts1755007801187

                    assign internal_w_ts1755007801184 = inj_unused_in_1755007801169_956;
                    assign inj_dout_1755007801184_740       = internal_w_ts1755007801184;
                    // END: ContinuousWire_ts1755007801184

                always_ff @(posedge clk or posedge reset) begin
                    if (reset) begin
                        ff_reg_ts1755007801181 <= START_VAL;
                        inj_out1_1755007801181_3 <= '0;
                        inj_out2_1755007801181_397 <= '0;
                        unused_int_var_ts1755007801181 <= 0;
                    end else begin
                        case ({inj_in1_1755007801181_131, inj_in2_1755007801181_444})
                            8'h00: ff_reg_ts1755007801181 <= ff_reg_ts1755007801181;
                            8'h01: ff_reg_ts1755007801181 <= inj_in1_1755007801181_131 + inj_in2_1755007801181_444;
                            default: ff_reg_ts1755007801181 <= MAX_COUNT;
                        endcase
                        inj_out1_1755007801181_3 <= ff_reg_ts1755007801181;
                        inj_out2_1755007801181_397 <= {inj_in1_1755007801181_131[0], inj_in1_1755007801181_131[0], inj_in1_1755007801181_131[0], inj_in1_1755007801181_131[0]} | {inj_in2_1755007801181_444[3], inj_in2_1755007801181_444[2], inj_in2_1755007801181_444[1], inj_in2_1755007801181_444[0]};
                    end
                end
                // END: ModuleFF_ts1755007801181

                // BEGIN: GenerateFor_ts1755007801179
                genvar i;
                generate
                    for (i = 0; i < 4; i = i + 1) begin : g_loop
                        assign inj_data_out_1755007801179_411[i] = inj_in_h_1755007801167_242[i];
                    end
                endgenerate
                // END: GenerateFor_ts1755007801179

                // BEGIN: SimpleAssign_ts1755007801177
                assign inj_out_data_1755007801176_810 = split_reg_var_ts1755007801168;
                // END: SimpleAssign_ts1755007801177

            always_comb begin
                inj_non_ansi_b_1755007801174_225_ts1755007801175 = reset_ts1755007801175;
                inj_non_ansi_basic_output_1755007801174_406_ts1755007801175 = inj_unused_in_1755007801169_956_ts1755007801175;
            end
            // END: non_ansi_basic_ts1755007801175

            // BEGIN: ImplicitTimeScaleModule_ts1755007801173
            assign inj_out_its_1755007801173_390 = inj_unused_in_1755007801169_956;
            // END: ImplicitTimeScaleModule_ts1755007801173

        always @(*) begin
            data_array_ts1755007801172[0] = inj_in_array_data_1755007801172_375[3:0];
            data_array_ts1755007801172[1] = inj_in_array_data_1755007801172_375[7:4];
            data_array_ts1755007801172[2] = 4'd8;
            data_array_ts1755007801172[3] = 4'd12;
        end
        assign inj_out_element_1755007801172_161 = data_array_ts1755007801172[inj_select_idx_1755007801172_541];
        // END: unpacked_array_module_ts1755007801172

        ModMultipleAlways ModMultipleAlways_inst_1755007801171_5397 (
            .dout_a(inj_dout_a_1755007801171_32),
            .dout_b(inj_dout_b_1755007801171_899),
            .clk_a(clk),
            .clk_b(clk),
            .din_a(inj_in_k_1755007801170_574),
            .din_b(inj_unused_in_1755007801169_956),
            .rst_n(reset)
        );
        LintLatch LintLatch_inst_1755007801170_1087 (
            .in_j(inj_unused_in_1755007801169_956),
            .in_k(inj_in_k_1755007801170_574),
            .out_l(inj_out_l_1755007801170_301)
        );
        // BEGIN: unreferenced_module_ts1755007801169
        assign inj_unused_out_1755007801169_670 = ~inj_unused_in_1755007801169_956;
        // END: unreferenced_module_ts1755007801169

        // BEGIN: case_single_default_after_item_ts1755007801169
        always_comb begin
            inj_out_res_1755007801169_382 = 1'b0;
            case (inj_in_val_1755007801169_808)
                2'b01: inj_out_res_1755007801169_382 = 1'b1;
                default: inj_out_res_1755007801169_382 = 1'b0;
                2'b10: inj_out_res_1755007801169_382 = 1'b1;
            endcase
        end
        // END: case_single_default_after_item_ts1755007801169

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_reg_var_ts1755007801168 <= 8'b0;
            other_reg_var_ts1755007801168 <= 8'b0;
            inj_out_reg_a_1755007801168_543 <= 8'b0;
            inj_out_reg_b_1755007801168_105 <= 8'b0;
        end else begin
            split_reg_var_ts1755007801168 <= inj_in_val_b_l_1755007801167_353;
            other_reg_var_ts1755007801168 <= inj_in_val_b_l_1755007801167_353 + 2;
            inj_out_reg_a_1755007801168_543 <= split_reg_var_ts1755007801168;
            inj_out_reg_b_1755007801168_105 <= other_reg_var_ts1755007801168;
        end
    end
    // END: mod_split_ff_ts1755007801168

    assign inj_out_c_1755007801167_178 = {inj_in_h_1755007801167_242, inj_in_l_1755007801167_208};
    // END: concat_op_ts1755007801167

    always @(*) begin
        inj_out_val_c_l_1755007801167_825 = inj_in_val_a_l_1755007801167_383 + inj_in_val_b_l_1755007801167_353;
        inj_out_val_d_l_1755007801167_479 = inj_in_val_a_l_1755007801167_383 - inj_in_val_b_l_1755007801167_353;
    end
    // END: split_inputs_outputs_only_ts1755007801167
endmodule

