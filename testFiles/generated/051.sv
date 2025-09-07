interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module PragmaProtectOptions (
    input int config_data_in,
    output int config_data_out
);
`ifdef SLANG_PRAGMA
`protect encoding (enctype="base64", line_length=76, bytes=1024)
`endif
`ifdef SLANG_PRAGMA
`protect license (library="my_project_lib", entry="start_feature_A", match=42, feature="feature_set_B", exit="end_feature_A")
`endif
`ifdef SLANG_PRAGMA
`protect reset
`endif
`ifdef SLANG_PRAGMA
`protect viewport (object="design.module_a.instance_b.register_c", access="read-only")
`endif
assign config_data_out = config_data_in + 1;
endmodule

module PragmaSyntaxVariety (
    input logic [1:0] test_case_mode,
    output logic [3:0] test_case_result
);
`ifdef SLANG_PRAGMA
`unknown_pragma_real 1.23;
`endif
`ifdef SLANG_PRAGMA
`unknown_slang_pragma (arg1, arg2="value")
`endif
`ifdef SLANG_PRAGMA
`protect (1 + 2)
`endif
`ifdef SLANG_PRAGMA
`protect {3, 4}
`endif
`ifdef SLANG_PRAGMA
`protect unknown_action (arg=1)
`endif
`ifdef SLANG_PRAGMA
`protect encoding
`endif
`ifdef SLANG_PRAGMA
`protect encoding (enctype="raw", "string_arg_only")
`endif
`ifdef SLANG_PRAGMA
`protect encoding (enctype="raw", unknown_option=99)
`endif
`ifdef SLANG_PRAGMA
`protect encoding (bytes=-10)
`endif
`ifdef SLANG_PRAGMA
`protect license (match="not_an_integer")
`endif
`ifdef SLANG_PRAGMA
`protect license (match=42.5)
`endif
`ifdef SLANG_PRAGMA
`protect viewport (obj="a", acc="b", extra=1)
`endif
`ifdef SLANG_PRAGMA
`protect begin (arg_present)
`endif
`ifdef SLANG_PRAGMA
`protect license ("license_string_only")
`endif
`ifdef SLANG_PRAGMA
`protect license (library=my_library_ident)
`endif
`ifdef SLANG_PRAGMA
`protect viewport (obj="a")
`endif
`ifdef SLANG_PRAGMA
`protect viewport (obj="a", acc="b", c=3)
`endif
`ifdef SLANG_PRAGMA
`protect viewport (obj="a", "access_string")
`endif
`ifdef SLANG_PRAGMA
`protect viewport ("object_string", acc="b")
`endif
`ifdef SLANG_PRAGMA
`protect viewport (object="a", access=123)
`endif
`ifdef SLANG_PRAGMA
`protect viewport (object=123, access="b")
`endif
`ifdef SLANG_PRAGMA
`protect viewport (not_object="a", access="b")
`endif
`ifdef SLANG_PRAGMA
`protect viewport (object="a", not_access="b")
`endif
`ifdef SLANG_PRAGMA
`diagnostic (1 + 2)
`endif
`ifdef SLANG_PRAGMA
`diagnostic unknown_action_diag
`endif
`ifdef SLANG_PRAGMA
`diagnostic level=warn
`endif
`ifdef SLANG_PRAGMA
`diagnostic ignore (value=(1+2))
`endif
`ifdef SLANG_PRAGMA
`diagnostic ignore (value=(value=1))
`endif
`ifdef SLANG_PRAGMA
`diagnostic ignore (value=some_identifier)
`endif
`ifdef SLANG_PRAGMA
`diagnostic warn (value=12345)
`endif
`ifdef SLANG_PRAGMA
`diagnostic ignore simple_identifier_arg
`endif
`ifdef SLANG_PRAGMA
`protect "simple_string_argument"
`endif
`ifdef SLANG_PRAGMA
`diagnostic ignore "just_a_string_diag_code"
`endif
assign test_case_result = (test_case_mode == 2'b01) ? 4'h5 : 4'hA;
endmodule

module mod_fixup_target (
    input logic fs_in_target,
    output logic fs_out_target
);
    assign fs_out_target = fs_in_target;
endmodule

module mod_fixup_syntax_user (
    input logic fs_in,
    output wire fs_out
);
    logic fixup_out_val;
    mod_fixup_target fixup_inst (
        .fs_in_target(fs_in),
        .fs_out_target(fixup_out_val)
    );
    assign fs_out = fixup_out_val;
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module snippet (
    input wire clk,
    input wire [1:0] inj_byte_idx_1755007768525_210,
    input logic [1:0] inj_case_sel_fmt_1755007768512_108,
    input int inj_config_data_in_1755007768533_634,
    input logic [3:0] inj_control_1755007768537_877,
    input logic [7:0] inj_data_in_fmt_1755007768512_243,
    input logic inj_i_in_1755007768512_186,
    input wire [31:0] inj_wide_data_1755007768525_955,
    input wire reset,
    output logic inj_case_output_ready_1755007768516_265,
    output int inj_config_data_out_1755007768533_686,
    output logic [7:0] inj_data_out_fmt_1755007768512_486,
    output wire inj_fs_out_1755007768520_566,
    output logic inj_o_out_1755007768512_700,
    output logic inj_o_out_1755007768514_571,
    output logic inj_o_reg_out_1755007768551_832,
    output wire inj_o_wire_out_1755007768551_368,
    output logic [7:0] inj_out_a_1755007768543_355,
    output logic [7:0] inj_out_b_1755007768543_993,
    output logic [7:0] inj_out_diff_m2_1755007768529_883,
    output logic [7:0] inj_out_q_1755007768522_292,
    output logic [7:0] inj_result1_1755007768537_197,
    output logic [7:0] inj_result2_1755007768537_286,
    output reg [7:0] inj_selected_byte_1755007768525_364,
    output logic [3:0] inj_test_case_result_1755007768515_729,
    output logic [7:0] inj_var_out_m2_1755007768529_881
);
    // BEGIN: name_conflict_example_ts1755007768512
    parameter int my_param = 5;
    logic my_var_ts1755007768512;
        // BEGIN: formatting_stress_ts1755007768513
        logic [7:0] temp_reg_fmt_ts1755007768513; 
        always_comb begin : stress_comb_block_label 
            inj_data_out_fmt_1755007768512_486 = 8'hXX; 
            if (my_var_ts1755007768512) begin
                if (inj_i_in_1755007768512_186) begin
                    case (inj_case_sel_fmt_1755007768512_108) 
                        2'b00: inj_data_out_fmt_1755007768512_486 = inj_data_in_fmt_1755007768512_243;
                        2'b01: begin 
                            inj_data_out_fmt_1755007768512_486 = ~inj_data_in_fmt_1755007768512_243; 
                            end 
                        2'b10: begin 
                            logic [7:0] added_val_ts1755007768513; 
                                // BEGIN: attributes_on_expr_port_ts1755007768514
                                logic internal_sig_ts1755007768514;
                                    // BEGIN: expr_postsub_comb_ts1755007768529
                                    logic [7:0] var_m2_ts1755007768529;
                                        // BEGIN: mod_split_comb_ts1755007768544
                                        logic [7:0]  split_comb_var_ts1755007768543;
                                        logic [7:0] other_comb_var_ts1755007768543;
                                            // BEGIN: nets_alias_clocking_ts1755007768551
                                            wire  w_internal_ts1755007768551;
                                            logic r_internal_ts1755007768551;
                                            assign w_internal_ts1755007768551  = reset & internal_sig_ts1755007768514;
                                            assign inj_o_wire_out_1755007768551_368  = w_internal_ts1755007768551;
                                            always_ff @(posedge clk) r_internal_ts1755007768551 <= my_var_ts1755007768512;
                                            assign inj_o_reg_out_1755007768551_832 = r_internal_ts1755007768551;
                                            // END: nets_alias_clocking_ts1755007768551

                                        always_comb begin
                                            split_comb_var_ts1755007768543 = 8'b0; 
                                            other_comb_var_ts1755007768543 = 8'b0;
                                            if (my_var_ts1755007768512) begin
                                                split_comb_var_ts1755007768543 = added_val_ts1755007768513;
                                                other_comb_var_ts1755007768543 = added_val_ts1755007768513 + 1;
                                            end
                                            inj_out_a_1755007768543_355 = split_comb_var_ts1755007768543;
                                            inj_out_b_1755007768543_993 = other_comb_var_ts1755007768543;
                                        end
                                        // END: mod_split_comb_ts1755007768544

                                        // BEGIN: dup_cond_ts1755007768538
                                        always_comb begin
                                            inj_result1_1755007768537_197 = '0;
                                            inj_result2_1755007768537_286 = '0;
                                            if (inj_control_1755007768537_877[0]) begin
                                                inj_result1_1755007768537_197 = var_m2_ts1755007768529 + inj_data_in_fmt_1755007768512_243;
                                            end else begin
                                                inj_result1_1755007768537_197 = var_m2_ts1755007768529 - inj_data_in_fmt_1755007768512_243;
                                            end
                                            if (inj_control_1755007768537_877[1]) begin
                                                inj_result2_1755007768537_286 = var_m2_ts1755007768529 - inj_data_in_fmt_1755007768512_243;
                                            end else begin
                                                inj_result2_1755007768537_286 = var_m2_ts1755007768529 + inj_data_in_fmt_1755007768512_243;
                                            end
                                            case (inj_control_1755007768537_877[3:2])
                                                2'b00: inj_result1_1755007768537_197 = var_m2_ts1755007768529 & inj_data_in_fmt_1755007768512_243;
                                                2'b01: inj_result1_1755007768537_197 = var_m2_ts1755007768529 | inj_data_in_fmt_1755007768512_243;
                                                2'b10: inj_result2_1755007768537_286 = var_m2_ts1755007768529 & inj_data_in_fmt_1755007768512_243;
                                                2'b11: inj_result2_1755007768537_286 = var_m2_ts1755007768529 | inj_data_in_fmt_1755007768512_243;
                                                default: begin inj_result1_1755007768537_197 = '0; inj_result2_1755007768537_286 = '0; end
                                            endcase
                                            if (inj_control_1755007768537_877[0] == inj_control_1755007768537_877[1]) begin
                                                inj_result1_1755007768537_197 = inj_result1_1755007768537_197 + 1;
                                            end else if (inj_control_1755007768537_877[2] != inj_control_1755007768537_877[3]) begin
                                                inj_result2_1755007768537_286 = inj_result2_1755007768537_286 - 1;
                                            end
                                        end
                                        // END: dup_cond_ts1755007768538

                                        PragmaProtectOptions PragmaProtectOptions_inst_1755007768533_1771 (
                                            .config_data_out(inj_config_data_out_1755007768533_686),
                                            .config_data_in(inj_config_data_in_1755007768533_634)
                                        );
                                    always_comb begin
                                        var_m2_ts1755007768529 = inj_data_in_fmt_1755007768512_243;
                                        inj_out_diff_m2_1755007768529_883 = (var_m2_ts1755007768529--) - added_val_ts1755007768513;
                                        inj_var_out_m2_1755007768529_881 = var_m2_ts1755007768529;
                                    end
                                    // END: expr_postsub_comb_ts1755007768529

                                    // BEGIN: Bit_Manip_ts1755007768526
                                    always_comb begin
                                        case (inj_byte_idx_1755007768525_210)
                                            2'b00: inj_selected_byte_1755007768525_364 = inj_wide_data_1755007768525_955[7:0];
                                            2'b01: inj_selected_byte_1755007768525_364 = inj_wide_data_1755007768525_955[15:8];
                                            2'b10: inj_selected_byte_1755007768525_364 = inj_wide_data_1755007768525_955[23:16];
                                            default: inj_selected_byte_1755007768525_364 = inj_wide_data_1755007768525_955[31:24];
                                        endcase
                                    end
                                    // END: Bit_Manip_ts1755007768526

                                    // BEGIN: split_single_stmt_ts1755007768522
                                    always @(*) begin
                                        inj_out_q_1755007768522_292 = added_val_ts1755007768513 + 1;
                                    end
                                    // END: split_single_stmt_ts1755007768522

                                    mod_fixup_syntax_user mod_fixup_syntax_user_inst_1755007768520_7108 (
                                        .fs_out(inj_fs_out_1755007768520_566),
                                        .fs_in(internal_sig_ts1755007768514)
                                    );
                                    // BEGIN: module_case_write_ts1755007768517
                                    my_if case_vif_inst();
                                    always_comb begin
                                        case (inj_case_sel_fmt_1755007768512_108)
                                            2'b00: begin
                                                case_vif_inst.data = 8'hAA;
                                                case_vif_inst.valid = 1'b1;
                                                case_vif_inst.ready = 1'b0;
                                            end
                                            2'b01: begin
                                                case_vif_inst.data = inj_data_in_fmt_1755007768512_243;
                                                case_vif_inst.valid = 1'b0;
                                                case_vif_inst.ready = 1'b1;
                                            end
                                            2'b10: begin
                                                case_vif_inst.data = added_val_ts1755007768513;
                                                case_vif_inst.valid = 1'b1;
                                                case_vif_inst.ready = 1'b1;
                                            end
                                            default: begin
                                                case_vif_inst.data = 8'hFF;
                                                case_vif_inst.valid = 1'b0;
                                                case_vif_inst.ready = 1'b0;
                                            end
                                        endcase
                                        inj_case_output_ready_1755007768516_265 = case_vif_inst.ready;
                                    end
                                    // END: module_case_write_ts1755007768517

                                    PragmaSyntaxVariety PragmaSyntaxVariety_inst_1755007768515_8909 (
                                        .test_case_mode(inj_case_sel_fmt_1755007768512_108),
                                        .test_case_result(inj_test_case_result_1755007768515_729)
                                    );
                                assign internal_sig_ts1755007768514 = inj_i_in_1755007768512_186 & my_var_ts1755007768512;
                                simple_adder sa_inst(
                                    .a  (inj_i_in_1755007768512_186),
                                    (* fanout_limit = 10 *) .b(my_var_ts1755007768512),
                                    .sum(inj_o_out_1755007768514_571)
                                );
                                // END: attributes_on_expr_port_ts1755007768514

                            added_val_ts1755007768513 = inj_data_in_fmt_1755007768512_243 + 8'h01; 
                            inj_data_out_fmt_1755007768512_486 = added_val_ts1755007768513; 
                            end 
                        default: inj_data_out_fmt_1755007768512_486 = 8'hFF; 
                    endcase 
                end else begin
                    inj_data_out_fmt_1755007768512_486 = inj_data_in_fmt_1755007768512_243 - 8'h01; 
                end 
            end else begin
                inj_data_out_fmt_1755007768512_486 = 8'h00; 
            end 
        end
        // END: formatting_stress_ts1755007768513

    always_comb my_var_ts1755007768512 = inj_i_in_1755007768512_186;
    assign inj_o_out_1755007768512_700 = inj_i_in_1755007768512_186 && (my_param == 5) && my_var_ts1755007768512;
    // END: name_conflict_example_ts1755007768512
endmodule

