module ComplexConversions (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic [15:0] out_concat
);
    always_comb begin
        out_concat = {in_a, in_b};
    end
endmodule

module LintAsyncFovIssue (
    input logic clk,
    input logic in_h,
    input logic rst_n,
    output logic out_i
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            out_i <= 1'b0;
        end else begin
            out_i <= in_h & out_i;
        end
    end
endmodule

module Module_BasicSyntax (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic out_cmp,
    output logic [7:0] out_ops
);
    logic [7:0] temp;
    always_comb begin
        temp = in_a + in_b;
    end
    assign out_ops = (in_a & in_b) | (in_a ^ in_b);
    assign out_cmp = (in_a == in_b);
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

module casez_xz_alt (
    input logic [2:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            3'b1?z: out_res = 1'b1;
            3'b0z?: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module child_scalar_port (
    input logic data_in,
    output logic data_out
);
    assign data_out = data_in;
endmodule

module cu_timeunit_mod (
    input logic clk,
    output logic reset
);
    logic internal_sig;
    always_ff @(posedge clk) begin
        reset <= 1'b0;
        internal_sig = clk;
    end
endmodule

module extern_declarations (
    input logic i_in,
    output logic o_out
);
    assign o_out = i_in;
endmodule

module mod_case_standard (
    input bit [7:0] in_cmd,
    output bit [3:0] out_status
);
always_comb begin
    case (in_cmd)
        8'd0, 8'd1, 8'd2: begin
            out_status = 4'hA;
        end
        8'd3, 8'd4: begin
            out_status = 4'hB;
        end
        default: begin
            out_status = 4'hF;
        end
    endcase
end
endmodule

module mod_casex_wildcard_overlap_priority (
    input bit [3:0] in_mask_x,
    output bit [1:0] out_match_type_x
);
always_comb begin
    out_match_type_x = 2'b01;
    priority casex (in_mask_x)
        4'b1X0Z: begin
            out_match_type_x = 2'b10;
        end
        4'b10?Z: begin
            out_match_type_x = 2'b11;
        end
        4'bZ1?X: begin
            out_match_type_x = 2'b00;
        end
        default: begin
            out_match_type_x = 2'b01;
        end
    endcase
end
endmodule

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

module mod_split_if (
    input logic clk,
    input logic cond,
    input logic [7:0] data_in,
    input logic reset,
    output logic [7:0] out_if_a,
    output logic [7:0] out_if_b
);
    logic [7:0]  split_if_var;
    logic [7:0] other_if_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_if_var <= 8'b0;
            other_if_var <= 8'b0;
        end else begin
            if (cond) begin
                split_if_var <= data_in;
                other_if_var <= data_in + 3;
            end else begin
                split_if_var <= data_in - 1;
                other_if_var <= data_in - 2;
            end
        end
    end
    always_comb begin
        out_if_a = split_if_var;
        out_if_b = other_if_var;
    end
endmodule

module mod_split_nested (
    input logic clk,
    input logic cond1,
    input logic cond2,
    input logic [7:0] data_in,
    input logic reset,
    output logic [7:0] out_nested_a,
    output logic [7:0] out_nested_b
);
    logic [7:0]  split_nested_var;
    logic [7:0] other_nested_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_nested_var <= 8'b0;
            other_nested_var <= 8'b0;
        end else begin
            split_nested_var <= 8'h11; 
            other_nested_var <= 8'h22; 
            if (cond1) begin
                split_nested_var <= data_in + 10;
                other_nested_var <= data_in + 20;
                if (cond2) begin
                    split_nested_var <= data_in + 100;
                    other_nested_var <= data_in + 200;
                end
            end else begin
                split_nested_var <= data_in - 10;
                other_nested_var <= data_in - 20;
            end
        end
    end
    always_comb begin
        out_nested_a = split_nested_var;
        out_nested_b = other_nested_var;
    end
endmodule

module module_simple (
    input wire i_a,
    input wire i_b,
    output wire o_c
);
    wire internal_xor_res;
    assign internal_xor_res = i_a ^ i_b;
    assign o_c = internal_xor_res & i_a;
endmodule

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module nets_alias_clocking (
    input logic i_clk,
    input logic i_data_sync,
    input logic i_reg_data,
    input wire i_wire_data,
    output logic o_reg_out,
    output wire o_wire_out
);
    wire  w_internal;
    logic r_internal;
    assign w_internal  = i_wire_data & i_reg_data;
    assign o_wire_out  = w_internal;
    always_ff @(posedge i_clk) r_internal <= i_data_sync;
    assign o_reg_out = r_internal;
endmodule

module super_outside_class_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module snippet (
    input wire clk,
    input logic inj_cond2_1755007916277_835,
    input wire [2:0] inj_count_in_1755007916453_43,
    input logic [3:0] inj_data_in_1755007916278_529,
    input logic [15:0] inj_dividend_mod_1755007916319_167,
    input logic inj_i_in_1755007916272_246,
    input wire [3:0] inj_in0_1755007916396_114,
    input wire [3:0] inj_in1_1755007916396_462,
    input wire [3:0] inj_in2_1755007916396_814,
    input wire [7:0] inj_in2_1755007916465_873,
    input wire [3:0] inj_in3_1755007916396_833,
    input bit inj_in_bit_1755007916358_452,
    input bit [7:0] inj_in_cmd_1755007916382_253,
    input wire [1:0] inj_in_const_index_1755007916300_537,
    input wire [7:0] inj_in_data_1755007916300_357,
    input wire [1:0] inj_in_index_1755007916300_969,
    input bit [3:0] inj_in_mask_x_1755007916271_361,
    input int inj_in_val_1755007916271_868,
    input logic [2:0] inj_in_val_1755007916310_885,
    input logic [1:0] inj_large_data_in_1755007916272_938,
    input logic [15:0] inj_numerator_1755007916319_832,
    input logic [31:0] inj_wide_data_in_1755007916284_689,
    input wire reset,
    output wire [2:0] inj_count_out_1755007916453_4,
    output bit inj_crypto_active_1755007916432_760,
    output logic [3:0] inj_data_out1_n_1755007916280_731,
    output logic [3:0] inj_data_out2_n_1755007916280_471,
    output logic [7:0] inj_data_out_1755007916278_384,
    output logic inj_data_out_1755007916344_506,
    output logic [15:0] inj_data_out_1755007916366_335,
    output logic [3:0] inj_data_out_1755007916403_203,
    output logic [7:0] inj_data_out_pa_1755007916334_500,
    output logic [3:0] inj_data_out_pv_1755007916334_938,
    output wire inj_dout_1755007916291_409,
    output logic [4:0] inj_internal_out_1755007916286_675,
    output logic [4:0] inj_internal_out_1755007916288_580,
    output logic [4:0] inj_internal_out_1755007916294_246,
    output logic [7:0] inj_large_sum_out_1755007916272_646,
    output reg [3:0] inj_mux_out_1755007916396_584,
    output wire inj_o_c_1755007916282_640,
    output logic inj_o_out_1755007916272_348,
    output logic inj_o_out_1755007916323_422,
    output logic inj_o_reg_out_1755007916297_509,
    output logic inj_o_reg_out_1755007916338_986,
    output logic [7:0] inj_o_result_1755007916305_931,
    output logic inj_o_status_1755007916305_880,
    output wire inj_o_wire_out_1755007916297_169,
    output wire inj_o_wire_out_1755007916338_248,
    output wire [7:0] inj_out1_1755007916465_428,
    output wire [7:0] inj_out2_1755007916465_880,
    output logic [7:0] inj_out_1755007916315_132,
    output logic [7:0] inj_out_array_sel_const_1755007916300_940,
    output logic [7:0] inj_out_array_sel_var_1755007916300_124,
    output logic inj_out_cmp_1755007916418_430,
    output logic [15:0] inj_out_concat_1755007916390_885,
    output logic [15:0] inj_out_concat_1755007916410_471,
    output logic [7:0] inj_out_diff_m2_1755007916425_666,
    output logic inj_out_i_1755007916330_817,
    output logic [7:0] inj_out_if_a_1755007916275_154,
    output logic [7:0] inj_out_if_b_1755007916275_902,
    output logic inj_out_logic_1755007916358_484,
    output bit [1:0] inj_out_match_type_x_1755007916271_669,
    output bit [1:0] inj_out_match_type_z_1755007916275_853,
    output logic [7:0] inj_out_nested_a_1755007916277_125,
    output logic [7:0] inj_out_nested_b_1755007916277_293,
    output logic [7:0] inj_out_ops_1755007916418_30,
    output logic [7:0] inj_out_reg_a_1755007916273_157,
    output logic [7:0] inj_out_reg_b_1755007916273_806,
    output reg inj_out_res_1755007916310_497,
    output logic [7:0] inj_out_slice_be_1755007916374_805,
    output logic [7:0] inj_out_slice_le_1755007916374_577,
    output bit [3:0] inj_out_status_1755007916382_180,
    output int inj_out_val_1755007916271_416,
    output int inj_out_val_1755007916272_472,
    output logic [7:0] inj_out_val_c_1755007916480_303,
    output logic [7:0] inj_out_x_j_1755007916351_601,
    output logic [7:0] inj_out_y_j_1755007916351_283,
    output wire inj_p_out_1755007916327_498,
    output logic [15:0] inj_quotient_1755007916319_11,
    output logic [15:0] inj_quotient_1755007916441_264,
    output logic [7:0] inj_remainder_1755007916319_528,
    output logic [7:0] inj_remainder_1755007916441_484,
    output logic inj_reset_1755007916272_641,
    output logic [7:0] inj_var_out_m2_1755007916425_626,
    output logic [31:0] inj_wide_data_out_1755007916284_406
);
    // BEGIN: local_not_allowed_diag_mod_ts1755007916272
    // BEGIN: loop_unroll_limit_test_ts1755007916273
    logic [7:0] current_large_sum_ts1755007916273;
        // BEGIN: mod_split_ff_ts1755007916274
        logic [7:0]  split_reg_var_ts1755007916274;
        logic [7:0] other_reg_var_ts1755007916274;
            // BEGIN: ModSampledVarLogic_ts1755007916278
            logic [7:0] __Vsampled_state = 8'hAB; 
            logic [7:0] internal_reg_ts1755007916278;
                // BEGIN: split_multiple_blocking_ts1755007916280
                logic [3:0] temp_n_ts1755007916280;
                    // BEGIN: ContinuousWire_ts1755007916291
                    wire internal_w_ts1755007916291;
                        // BEGIN: Mod_ArrayOps_ts1755007916301
                        logic [7:0] my_array_ts1755007916301 [3:0];
                            // BEGIN: explicit_non_ansi_decl_module_ts1755007916327
                            input logic inj_cond2_1755007916277_835_ts1755007916327;
                            output wire inj_p_out_1755007916327_498_ts1755007916327;
                                // BEGIN: module_packed_variables_ts1755007916334
                                logic [31:0] data_pv_ts1755007916334 ;
                                    // BEGIN: sequential_logic_ts1755007916403
                                    ;
                                    logic [3:0] internal_reg_ts1755007916403;
                                        // BEGIN: expr_postsub_comb_ts1755007916425
                                        logic [7:0] var_m2_ts1755007916425;
                                            // BEGIN: simple_seq_ts1755007916453
                                            reg [2:0] counter_reg_ts1755007916453;
                                                // BEGIN: multi_always_comb_ts1755007916466
                                                logic [7:0] intermediate1_ts1755007916466;
                                                logic [7:0] intermediate2_ts1755007916466;
                                                    // BEGIN: split_seq_dependency_ts1755007916480
                                                    logic [7:0] mid_val_c_ts1755007916480;
                                                    always @(posedge clk) begin
                                                        mid_val_c_ts1755007916480 <= other_reg_var_ts1755007916274 + 1;
                                                        inj_out_val_c_1755007916480_303 <= mid_val_c_ts1755007916480 * 2;
                                                    end
                                                    // END: split_seq_dependency_ts1755007916480

                                                always @(*) begin
                                                    intermediate1_ts1755007916466 = inj_in_data_1755007916300_357 & inj_in2_1755007916465_873;
                                                end
                                                always @(*) begin
                                                    intermediate2_ts1755007916466 = inj_in_data_1755007916300_357 | inj_in2_1755007916465_873;
                                                end
                                                assign inj_out1_1755007916465_428 = intermediate1_ts1755007916466 + 8'd1;
                                                assign inj_out2_1755007916465_880 = intermediate2_ts1755007916466 - 8'd1;
                                                // END: multi_always_comb_ts1755007916466

                                            always @(posedge clk or posedge reset) begin
                                                if (reset) begin
                                                    counter_reg_ts1755007916453 <= 3'b000;
                                                end else begin
                                                    counter_reg_ts1755007916453 <= inj_count_in_1755007916453_43 + 3'b001;
                                                end
                                            end
                                            assign inj_count_out_1755007916453_4 = counter_reg_ts1755007916453;
                                            // END: simple_seq_ts1755007916453

                                            // BEGIN: div_mod_ops_ts1755007916442
                                            assign inj_quotient_1755007916441_264 = (var_m2_ts1755007916425 == 0) ? 16'hFFFF : (inj_dividend_mod_1755007916319_167 / var_m2_ts1755007916425); 
                                            assign inj_remainder_1755007916441_484 = (split_reg_var_ts1755007916274 == 0) ? 8'hFF : (inj_numerator_1755007916319_832 % split_reg_var_ts1755007916274);
                                            // END: div_mod_ops_ts1755007916442

                                            // BEGIN: PragmaProtectKeyBlock_ts1755007916432
                                        `ifdef SLANG_PRAGMA
                                        `protect key
                                        `endif
                                        `ifdef SLANG_PRAGMA
                                        `protect block
                                        `endif
                                        assign inj_crypto_active_1755007916432_760 = inj_in_bit_1755007916358_452;
                                            // END: PragmaProtectKeyBlock_ts1755007916432

                                        always_comb begin
                                            var_m2_ts1755007916425 = current_large_sum_ts1755007916273;
                                            inj_out_diff_m2_1755007916425_666 = (var_m2_ts1755007916425--) - internal_reg_ts1755007916278;
                                            inj_var_out_m2_1755007916425_626 = var_m2_ts1755007916425;
                                        end
                                        // END: expr_postsub_comb_ts1755007916425

                                        Module_BasicSyntax Module_BasicSyntax_inst_1755007916418_521 (
                                            .out_cmp(inj_out_cmp_1755007916418_430),
                                            .out_ops(inj_out_ops_1755007916418_30),
                                            .in_a(current_large_sum_ts1755007916273),
                                            .in_b(other_reg_var_ts1755007916274)
                                        );
                                        ComplexConversions ComplexConversions_inst_1755007916410_7995 (
                                            .out_concat(inj_out_concat_1755007916410_471),
                                            .in_a(other_reg_var_ts1755007916274),
                                            .in_b(internal_reg_ts1755007916278)
                                        );
                                    always_ff @(posedge clk or negedge reset) begin
                                        if (!reset) begin
                                            internal_reg_ts1755007916403 <= 4'h0;
                                        end else begin
                                            internal_reg_ts1755007916403 <= temp_n_ts1755007916280;
                                        end
                                    end
                                    assign inj_data_out_1755007916403_203 = internal_reg_ts1755007916403;
                                    // END: sequential_logic_ts1755007916403

                                    // BEGIN: Comb_Case_ts1755007916396
                                    always_comb begin
                                        case (inj_in_const_index_1755007916300_537)
                                            2'b00: inj_mux_out_1755007916396_584 = inj_in0_1755007916396_114;
                                            2'b01: inj_mux_out_1755007916396_584 = inj_in1_1755007916396_462;
                                            2'b10: inj_mux_out_1755007916396_584 = inj_in2_1755007916396_814;
                                            default: inj_mux_out_1755007916396_584 = inj_in3_1755007916396_833;
                                        endcase
                                    end
                                    // END: Comb_Case_ts1755007916396

                                    ComplexConversions ComplexConversions_inst_1755007916390_559 (
                                        .in_a(other_reg_var_ts1755007916274),
                                        .in_b(my_array_ts1755007916301),
                                        .out_concat(inj_out_concat_1755007916390_885)
                                    );
                                    mod_case_standard mod_case_standard_inst_1755007916382_8227 (
                                        .in_cmd(inj_in_cmd_1755007916382_253),
                                        .out_status(inj_out_status_1755007916382_180)
                                    );
                                    // BEGIN: range_select_simple_packed_ts1755007916374
                                    assign inj_out_slice_be_1755007916374_805 = inj_dividend_mod_1755007916319_167[7:0]; 
                                    assign inj_out_slice_le_1755007916374_577 = inj_dividend_mod_1755007916319_167[7:0]; 
                                    // END: range_select_simple_packed_ts1755007916374

                                    // BEGIN: SequentialLogicPlaceholder_ts1755007916366
                                    always_ff @(posedge clk or posedge reset) begin
                                        if (reset) begin
                                            inj_data_out_1755007916366_335 <= 16'h0;
                                        end else begin
                                            inj_data_out_1755007916366_335 <= inj_numerator_1755007916319_832;
                                        end
                                    end
                                    // END: SequentialLogicPlaceholder_ts1755007916366

                                    // BEGIN: DummyHierModule_ts1755007916358
                                    assign inj_out_logic_1755007916358_484 = inj_in_bit_1755007916358_452;
                                    // END: DummyHierModule_ts1755007916358

                                    // BEGIN: split_multiple_in_branch_ts1755007916351
                                    always @(posedge clk) begin
                                        if (inj_i_in_1755007916272_246) begin
                                            inj_out_x_j_1755007916351_601 <= my_array_ts1755007916301 * 3;
                                            inj_out_y_j_1755007916351_283 <= other_reg_var_ts1755007916274 + 1;
                                        end else begin
                                            inj_out_x_j_1755007916351_601 <= my_array_ts1755007916301;
                                            inj_out_y_j_1755007916351_283 <= other_reg_var_ts1755007916274;
                                        end
                                    end
                                    // END: split_multiple_in_branch_ts1755007916351

                                    child_scalar_port child_scalar_port_inst_1755007916344_4017 (
                                        .data_out(inj_data_out_1755007916344_506),
                                        .data_in(inj_cond2_1755007916277_835_ts1755007916327)
                                    );
                                    nets_alias_clocking nets_alias_clocking_inst_1755007916338_2095 (
                                        .i_reg_data(inj_i_in_1755007916272_246),
                                        .i_wire_data(reset),
                                        .o_reg_out(inj_o_reg_out_1755007916338_986),
                                        .o_wire_out(inj_o_wire_out_1755007916338_248),
                                        .i_clk(clk),
                                        .i_data_sync(inj_cond2_1755007916277_835)
                                    );
                                logic [7:0] data_pa[0:1] ;
                                always_comb begin
                                    if (inj_cond2_1755007916277_835) begin
                                        data_pv_ts1755007916334[7:0] = split_reg_var_ts1755007916274;
                                        data_pv_ts1755007916334[15:8] = ~split_reg_var_ts1755007916274;
                                        data_pv_ts1755007916334[23:16] = data_pv_ts1755007916334[7:0];
                                        data_pv_ts1755007916334[31:24] = data_pv_ts1755007916334[15:8];
                                        data_pa[0] = inj_dividend_mod_1755007916319_167[7:0];
                                        data_pa[1] = inj_dividend_mod_1755007916319_167[15:8];
                                    end else begin
                                        data_pv_ts1755007916334 = 32'h0;
                                        data_pa[0] = 8'h0;
                                        data_pa[1] = 8'h0;
                                    end
                                end
                                assign inj_data_out_pv_1755007916334_938 = data_pv_ts1755007916334[3:0];
                                assign inj_data_out_pa_1755007916334_500 = data_pa[0];
                                // END: module_packed_variables_ts1755007916334

                                LintAsyncFovIssue LintAsyncFovIssue_inst_1755007916330_8633 (
                                    .rst_n(reset),
                                    .out_i(inj_out_i_1755007916330_817),
                                    .clk(clk),
                                    .in_h(inj_cond2_1755007916277_835)
                                );
                            assign inj_p_out_1755007916327_498_ts1755007916327 = inj_cond2_1755007916277_835_ts1755007916327;
                            // END: explicit_non_ansi_decl_module_ts1755007916327

                            // BEGIN: extern_declarations_ts1755007916323
                            assign inj_o_out_1755007916323_422 = inj_i_in_1755007916272_246;
                            // END: extern_declarations_ts1755007916323

                            // BEGIN: div_mod_ops_ts1755007916319
                            assign inj_quotient_1755007916319_11 = (internal_reg_ts1755007916278 == 0) ? 16'hFFFF : (inj_numerator_1755007916319_832 / internal_reg_ts1755007916278); 
                            assign inj_remainder_1755007916319_528 = (split_reg_var_ts1755007916274 == 0) ? 8'hFF : (inj_dividend_mod_1755007916319_167 % split_reg_var_ts1755007916274);
                            // END: div_mod_ops_ts1755007916319

                            // BEGIN: sequential_always_assign_ts1755007916315
                            always @(posedge clk) begin
                                inj_out_1755007916315_132 <= my_array_ts1755007916301;
                            end
                            // END: sequential_always_assign_ts1755007916315

                            casez_xz_alt casez_xz_alt_inst_1755007916310_7407 (
                                .in_val(inj_in_val_1755007916310_885),
                                .out_res(inj_out_res_1755007916310_497)
                            );
                            // BEGIN: bind_directive_top_ts1755007916305
                            target_module_for_bind target_inst(
                                .i_target_clk   (clk),
                                .i_target_data  (other_reg_var_ts1755007916274),
                                .o_target_result(inj_o_result_1755007916305_931)
                            );
                            module_to_bind bind_inst(
                                .i_bind_clk     (clk),
                                .i_bind_control (temp_n_ts1755007916280),
                                .o_bind_status  (inj_o_status_1755007916305_880)
                            );
                            // END: bind_directive_top_ts1755007916305

                        always_comb begin
                            my_array_ts1755007916301[0] = inj_in_data_1755007916300_357;
                            my_array_ts1755007916301[1] = inj_in_data_1755007916300_357 + 8'd1;
                            my_array_ts1755007916301[2] = inj_in_data_1755007916300_357 + 8'd2;
                            my_array_ts1755007916301[3] = inj_in_data_1755007916300_357 + 8'd3;
                            inj_out_array_sel_var_1755007916300_124 = my_array_ts1755007916301[inj_in_index_1755007916300_969];
                            inj_out_array_sel_const_1755007916300_940 = my_array_ts1755007916301[inj_in_const_index_1755007916300_537];
                        end
                        // END: Mod_ArrayOps_ts1755007916301

                        nets_alias_clocking nets_alias_clocking_inst_1755007916297_8255 (
                            .i_wire_data(reset),
                            .o_reg_out(inj_o_reg_out_1755007916297_509),
                            .o_wire_out(inj_o_wire_out_1755007916297_169),
                            .i_clk(clk),
                            .i_data_sync(inj_i_in_1755007916272_246),
                            .i_reg_data(inj_cond2_1755007916277_835)
                        );
                        case_full_simple_mod case_full_simple_mod_inst_1755007916294_1033 (
                            .case_expr(inj_large_data_in_1755007916272_938),
                            .internal_out(inj_internal_out_1755007916294_246)
                        );
                    assign internal_w_ts1755007916291 = inj_i_in_1755007916272_246;
                    assign inj_dout_1755007916291_409       = internal_w_ts1755007916291;
                    // END: ContinuousWire_ts1755007916291

                    // BEGIN: case_unique_casez_reordered_mod_ts1755007916289
                    always @* begin
                        unique casez ({inj_large_data_in_1755007916272_938[0], inj_data_in_1755007916278_529[3:2], inj_large_data_in_1755007916272_938[1]})
                            4'b1?0?: inj_internal_out_1755007916288_580 = 30;
                            4'b?101: inj_internal_out_1755007916288_580 = 31;  
                            4'b0?1?: inj_internal_out_1755007916288_580 = 32;
                            4'b1?1?: inj_internal_out_1755007916288_580 = 33;  
                            4'b?111: inj_internal_out_1755007916288_580 = 34;  
                        endcase
                    end
                    // END: case_unique_casez_reordered_mod_ts1755007916289

                    // BEGIN: case_unique_casez_reordered_mod_ts1755007916286
                    always @* begin
                        unique casez ({inj_large_data_in_1755007916272_938[0], inj_data_in_1755007916278_529[3:2], inj_large_data_in_1755007916272_938[1]})
                            4'b1?0?: inj_internal_out_1755007916286_675 = 30;
                            4'b?101: inj_internal_out_1755007916286_675 = 31;  
                            4'b0?1?: inj_internal_out_1755007916286_675 = 32;
                            4'b1?1?: inj_internal_out_1755007916286_675 = 33;  
                            4'b?111: inj_internal_out_1755007916286_675 = 34;  
                        endcase
                    end
                    // END: case_unique_casez_reordered_mod_ts1755007916286

                    // BEGIN: module_using_package_param_ts1755007916284
                    assign inj_wide_data_out_1755007916284_406 = inj_wide_data_in_1755007916284_689;
                    // END: module_using_package_param_ts1755007916284

                    module_simple module_simple_inst_1755007916282_5711 (
                        .i_b(reset),
                        .o_c(inj_o_c_1755007916282_640),
                        .i_a(clk)
                    );
                always @(*) begin
                    temp_n_ts1755007916280 = inj_data_in_1755007916278_529 + 1;
                    inj_data_out1_n_1755007916280_731 = temp_n_ts1755007916280 * 2;
                    inj_data_out2_n_1755007916280_471 = temp_n_ts1755007916280 + 3;
                end
                // END: split_multiple_blocking_ts1755007916280

            always @(posedge clk) begin
            if (inj_data_in_1755007916278_529 == 4'd5) begin 
                internal_reg_ts1755007916278 <= __Vsampled_state + inj_data_in_1755007916278_529; 
            end else if (inj_data_in_1755007916278_529 > 4'd8) begin 
                internal_reg_ts1755007916278 <= {4'h0, inj_data_in_1755007916278_529} - 1; 
            end else begin
                internal_reg_ts1755007916278 <= 8'hFF;
            end
            end
            assign inj_data_out_1755007916278_384 = internal_reg_ts1755007916278;
            // END: ModSampledVarLogic_ts1755007916278

            mod_split_nested mod_split_nested_inst_1755007916277_9084 (
                .reset(reset),
                .out_nested_a(inj_out_nested_a_1755007916277_125),
                .out_nested_b(inj_out_nested_b_1755007916277_293),
                .clk(clk),
                .cond1(inj_i_in_1755007916272_246),
                .cond2(inj_cond2_1755007916277_835),
                .data_in(current_large_sum_ts1755007916273)
            );
            mod_split_if mod_split_if_inst_1755007916276_3727 (
                .cond(inj_i_in_1755007916272_246),
                .data_in(split_reg_var_ts1755007916274),
                .reset(reset),
                .out_if_a(inj_out_if_a_1755007916275_154),
                .out_if_b(inj_out_if_b_1755007916275_902),
                .clk(clk)
            );
            mod_casez_wildcard mod_casez_wildcard_inst_1755007916275_2910 (
                .in_mask_z(inj_in_mask_x_1755007916271_361),
                .out_match_type_z(inj_out_match_type_z_1755007916275_853)
            );
        always_ff @(posedge clk or posedge reset) begin
            if (reset) begin
                split_reg_var_ts1755007916274 <= 8'b0;
                other_reg_var_ts1755007916274 <= 8'b0;
                inj_out_reg_a_1755007916273_157 <= 8'b0;
                inj_out_reg_b_1755007916273_806 <= 8'b0;
            end else begin
                split_reg_var_ts1755007916274 <= current_large_sum_ts1755007916273;
                other_reg_var_ts1755007916274 <= current_large_sum_ts1755007916273 + 2;
                inj_out_reg_a_1755007916273_157 <= split_reg_var_ts1755007916274;
                inj_out_reg_b_1755007916273_806 <= other_reg_var_ts1755007916274;
            end
        end
        // END: mod_split_ff_ts1755007916274

    always_comb begin
        current_large_sum_ts1755007916273 = 8'h00;
        for (int m = 0; m < 40; m = m + 1) begin 
            current_large_sum_ts1755007916273 = current_large_sum_ts1755007916273 + inj_large_data_in_1755007916272_938[0];
            current_large_sum_ts1755007916273 = current_large_sum_ts1755007916273 + inj_large_data_in_1755007916272_938[1];
            current_large_sum_ts1755007916273 = current_large_sum_ts1755007916273 + 1;
        end
        inj_large_sum_out_1755007916272_646 = current_large_sum_ts1755007916273;
    end
    // END: loop_unroll_limit_test_ts1755007916273

    assign inj_out_val_1755007916272_472 = inj_in_val_1755007916271_868;
    // END: local_not_allowed_diag_mod_ts1755007916272

    extern_declarations extern_declarations_inst_1755007916272_7799 (
        .i_in(inj_i_in_1755007916272_246),
        .o_out(inj_o_out_1755007916272_348)
    );
    cu_timeunit_mod cu_timeunit_mod_inst_1755007916272_9790 (
        .clk(clk),
        .reset(inj_reset_1755007916272_641)
    );
    mod_casex_wildcard_overlap_priority mod_casex_wildcard_overlap_priority_inst_1755007916271_2501 (
        .out_match_type_x(inj_out_match_type_x_1755007916271_669),
        .in_mask_x(inj_in_mask_x_1755007916271_361)
    );
    super_outside_class_diag_mod super_outside_class_diag_mod_inst_1755007916271_9046 (
        .in_val(inj_in_val_1755007916271_868),
        .out_val(inj_out_val_1755007916271_416)
    );
endmodule

