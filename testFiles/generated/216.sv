typedef struct packed {
    logic [3:0] f1;
    logic       f2;
    logic [2:0] f3;
} eight_bit_unpacked_struct_t;
typedef struct packed {
    logic [2:0] f3;
    logic [3:0] f1;
    logic f2;
} eight_bit_unpacked_struct_t;

module Comb_Loop (
    input wire loop_in,
    output wire loop_out
);
    wire loop_wire1;
    wire loop_wire2;
    assign loop_wire1 = loop_wire2 | loop_in;
    assign loop_wire2 = loop_wire1; 
    assign loop_out = loop_wire1;
endmodule

module ModuleBasic (
    input logic a,
    input int b,
    output logic out_a,
    output int out_b
);
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c;
    int   d;
    always_comb begin
        logic temp_v;
        temp_v = d;
        c      = temp_v;
    end
    assign out_a = a;
    assign d     = b;
    assign out_b = d + P1 + LP1;
endmodule

module PragmaDiagnosticDirective (
    input int diag_input_val,
    output bit diag_output_flag
);
`ifdef SLANG_PRAGMA
`diagnostic push
`endif
`ifdef SLANG_PRAGMA
`diagnostic ignore "SLANG_UNUSED_VARIABLE"
`endif
`ifdef SLANG_PRAGMA
`diagnostic warn "SLANG_IMPLICIT_CAST"
`endif
`ifdef SLANG_PRAGMA
`diagnostic error "SLANG_MULTIPLE_DRIVER"
`endif
`ifdef SLANG_PRAGMA
`diagnostic fatal "SLANG_SYNTAX_ERROR_FATAL"
`endif
`ifdef SLANG_PRAGMA
`diagnostic ignore (value=("SLANG_UNDRIVEN_SIGNAL", "SLANG_UNREAD_SIGNAL"))
`endif
`ifdef SLANG_PRAGMA
`diagnostic warn (value="SLANG_LATCH_INFERRED")
`endif
assign diag_output_flag = (diag_input_val > 0);
`ifdef SLANG_PRAGMA
`diagnostic pop
`endif
endmodule

module PragmaProtectKeyBlock (
    input bit enable_crypto,
    output bit crypto_active
);
`ifdef SLANG_PRAGMA
`protect key
`endif
`ifdef SLANG_PRAGMA
`protect block
`endif
assign crypto_active = enable_crypto;
endmodule

module basic_comb (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out1
);
    ;
    logic [7:0] temp_wire;
    assign temp_wire = in1 + in2;
    always_comb begin
        out1 = temp_wire;
    end
endmodule

module coalesced_assign (
    input logic [3:0] in_h,
    input logic [3:0] in_l,
    output logic [7:0] out
);
    wire [7:0] temp_wire;
    assign temp_wire[7:4] = in_h;
    assign temp_wire[3:0] = in_l;
    assign out = temp_wire;
endmodule

module combinatorial_logic (
    input logic [3:0] in_vector,
    output logic out_single
);
    always_comb begin
        if (in_vector > 4'd5) begin
            out_single = 1'b1;
        end else begin
            out_single = 1'b0;
        end
    end
endmodule

module definition_used_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
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

module mod_internal_if_test (
    input wire in_i,
    output logic out_o
);
    assign out_o = !in_i;
endmodule

module mod_module_attrs #(
    parameter int WIDTH = 8
) (
    input wire [7:0] i_in,
    output logic [7:0] o_out
);
    logic [WIDTH-1:0] r_data;
    always_comb begin
        r_data = i_in;
    end
    assign o_out = r_data;
endmodule

module split_complex_nb (
    input logic clk_s,
    input logic [7:0] i1_s,
    input logic [7:0] i2_s,
    input logic [7:0] i3_s,
    output logic [7:0] o1_s,
    output logic [7:0] o2_s,
    output logic [7:0] o3_s
);
    logic [7:0] t1_s, t2_s;
    always @(posedge clk_s) begin
        t1_s <= i1_s + i2_s;
        o1_s <= t1_s - i3_s;
        t2_s <= i2_s * i3_s;
        o2_s <= t1_s + t2_s;
        o3_s <= t2_s / 2;
    end
endmodule

module split_ifelse_chain (
    input logic c1_x,
    input logic c2_x,
    input logic c3_x,
    input logic clk_x,
    input logic [7:0] v1_x,
    input logic [7:0] v2_x,
    input logic [7:0] v3_x,
    input logic [7:0] v4_x,
    output logic [7:0] out_x
);
    always @(posedge clk_x) begin
        if (c1_x) begin
            out_x <= v1_x;
        end else if (c2_x) begin
            out_x <= v2_x;
        end else if (c3_x) begin
            out_x <= v3_x;
        end else begin
            out_x <= v4_x;
        end
    end
endmodule

module split_input_only_var (
    input logic clk_k,
    input logic control_signal_k,
    input logic [7:0] data_in_k,
    output logic [7:0] data_out_k
);
    always @(posedge clk_k) begin
        if (control_signal_k) begin
            data_out_k <= data_in_k;
        end
    end
endmodule

module snippet #(
    parameter integer DATA_WIDTH = 8,
    parameter int SEL_PARAM = 6
) (
    input wire clk,
    input bit inj_condition_m10_1755007825699_456,
    input logic [3:0] inj_data1_1755007825968_632,
    input logic [3:0] inj_data2_1755007825968_562,
    input int inj_data_in_1755007825668_282,
    input logic inj_data_in_1755007825669_956,
    input logic [7:0] inj_data_in_k_1755007825683_509,
    input wire [3:0] inj_dffcl_ctrl_mode_1755007825663_431,
    input wire [15:0] inj_dffcl_data_in1_1755007825663_95,
    input wire [15:0] inj_dffcl_data_in2_1755007825663_582,
    input logic inj_enable_in_1755007825669_7,
    input logic [15:0] inj_in1_1755007825667_1,
    input logic [15:0] inj_in2_1755007825667_769,
    input logic [15:0] inj_in3_1755007825667_304,
    input logic [15:0] inj_in4_1755007825667_805,
    input logic [15:0] inj_in5_1755007825667_889,
    input logic [7:0] inj_in_b_1755007825689_56,
    input bit [7:0] inj_in_cmd_1755007825737_280,
    input wire [7:0] inj_in_func_b_1755007825706_819,
    input logic [3:0] inj_in_l_1755007825904_317,
    input logic [38:0] inj_in_packed_for_conv_1755007825746_755,
    input logic [2:0] inj_in_val_1755007825672_814,
    input logic [3:0] inj_in_vector_1755007825671_783,
    input wire [7:0] inj_param_in_1755007825676_185,
    input logic inj_sel_1755007825696_661,
    input logic [1:0] inj_test_case_mode_1755007825680_69,
    input wire reset,
    output bit inj_crypto_active_1755007825919_434,
    output wire inj_data_b_1755007825674_312,
    output int inj_data_out_1755007825668_822,
    output logic inj_data_out_1755007825669_3,
    output logic [7:0] inj_data_out_1755007825729_878,
    output logic [3:0] inj_data_out_case_1755007825968_978,
    output logic [7:0] inj_data_out_k_1755007825683_90,
    output logic [7:0] inj_data_out_k_1755007825702_324,
    output logic [7:0] inj_data_out_pa_1755007825756_592,
    output logic [3:0] inj_data_out_pv_1755007825756_779,
    output logic [15:0] inj_dcac_end_val_1755007825709_193,
    output logic [15:0] inj_dffcl_data_out_1755007825663_808,
    output bit inj_diag_output_flag_1755007825825_769,
    output wire inj_loop_out_1755007825851_378,
    output logic [7:0] inj_o1_s_1755007825834_243,
    output logic [7:0] inj_o2_s_1755007825834_982,
    output logic [7:0] inj_o3_s_1755007825834_482,
    output logic [7:0] inj_o_out_1755007825678_977,
    output logic inj_o_out_1755007825777_607,
    output logic [7:0] inj_out1_1755007825723_939,
    output logic [7:0] inj_out1_1755007825934_469,
    output logic inj_out1_bind_def_1755007825686_491,
    output logic [7:0] inj_out1_dd_1755007825844_750,
    output logic [7:0] inj_out2_1755007825723_864,
    output logic [7:0] inj_out2_dd_1755007825844_879,
    output logic inj_out_1755007825667_872,
    output logic [7:0] inj_out_1755007825860_217,
    output logic [7:0] inj_out_1755007825873_310,
    output logic [7:0] inj_out_1755007825904_519,
    output logic inj_out_bit_conv_1755007825746_998,
    output logic inj_out_cmp_1755007825689_313,
    output logic [7:0] inj_out_func_result_1755007825706_323,
    output logic inj_out_g_1755007825950_76,
    output int inj_out_int_conv_1755007825745_924,
    output logic inj_out_o_1755007825807_233,
    output logic [7:0] inj_out_ops_1755007825689_880,
    output logic [7:0] inj_out_reg_h_1755007825940_299,
    output reg inj_out_res_1755007825672_833,
    output logic inj_out_single_1755007825671_98,
    output bit [3:0] inj_out_status_1755007825737_399,
    output bit [3:0] inj_out_status_1755007825766_378,
    output logic [7:0] inj_out_unpacked_struct_repacked_1755007825745_255,
    output int inj_out_val_1755007825815_876,
    output logic [7:0] inj_out_val_c_1755007825693_459,
    output logic [7:0] inj_out_val_m10_1755007825699_298,
    output logic [5:0] inj_out_vec_conv_1755007825745_937,
    output logic [7:0] inj_out_x_1755007825799_404,
    output logic [7:0] inj_output_bf_1755007825888_133,
    output logic [3:0] inj_output_bf_slice_1755007825888_515,
    output wire [7:0] inj_param_out_1755007825676_872,
    output logic inj_result_1755007825696_40,
    output logic inj_sub_out_1755007825787_338,
    output logic [3:0] inj_test_case_result_1755007825680_285
);
    // BEGIN: deep_ff_control_logic_ts1755007825666
    // BEGIN: arith_comp_ops_ts1755007825667
    // BEGIN: mod_named_begin_ts1755007825668
    // BEGIN: sequential_register_ts1755007825669
    // BEGIN: casez_xz_ts1755007825673
    // BEGIN: simple_logic_a_ts1755007825674
    // BEGIN: module_with_params_ts1755007825676
    // BEGIN: PragmaSyntaxVariety_ts1755007825681
`ifdef SLANG_PRAGMA
`unknown_pragma_real 1.23;
    // BEGIN: Module_BasicSyntax_ts1755007825689
    logic [7:0] temp_ts1755007825689;
        // BEGIN: split_seq_dependency_ts1755007825693
        logic [7:0] mid_val_c_ts1755007825693;
            // BEGIN: unsupported_cond_expr_ts1755007825699
            logic [7:0] var_m10_ts1755007825699;
                // BEGIN: module_function_ts1755007825706
                function automatic [7:0] add_and_subtract;
                input [7:0] val1;
                input [7:0] val2;
                reg [7:0] temp_ts1755007825706;
                    // BEGIN: deep_comb_assign_chain_ts1755007825717
                    logic [15:0] t1_ts1755007825710, t2_ts1755007825710, t3_ts1755007825710, t4_ts1755007825710, t5_ts1755007825710, t6_ts1755007825710, t7_ts1755007825710, t8_ts1755007825710, t9_ts1755007825710, t10_ts1755007825710;
                    logic [15:0] t11_ts1755007825710, t12_ts1755007825710, t13_ts1755007825710, t14_ts1755007825710, t15_ts1755007825710, t16_ts1755007825710, t17_ts1755007825710, t18_ts1755007825710, t19_ts1755007825710, t20_ts1755007825710;
                    logic [15:0] t21_ts1755007825710, t22_ts1755007825710, t23_ts1755007825710, t24_ts1755007825710, t25_ts1755007825710, t26_ts1755007825710, t27_ts1755007825710, t28_ts1755007825710, t29_ts1755007825710, t30_ts1755007825710;
                    logic [15:0] t31_ts1755007825710, t32_ts1755007825710, t33_ts1755007825710, t34_ts1755007825710, t35_ts1755007825710, t36_ts1755007825710, t37_ts1755007825710, t38_ts1755007825710, t39_ts1755007825710, t40_ts1755007825710;
                        // BEGIN: ModuleHierarchy_High_ts1755007825730
                        ModuleBasic m1 (
                            .a      (1'b1),
                            .b      (inj_data_in_1755007825668_282),
                            .out_a  (),
                            .out_b  ( )
                        );
                        if (SEL_PARAM > 5) begin : gen_high
                            int high_data_ts1755007825730;
                            ModuleBasic m_high (
                                .a      (1'b0),
                                .b      (SEL_PARAM),
                                .out_a  (),
                                .out_b  (high_data_ts1755007825730)
                            );
                        end else begin : gen_low
                            int low_data_ts1755007825730;
                            ModuleBasic m_low (
                                .a      (1'b0),
                                .b      (SEL_PARAM),
                                .out_a  (),
                                .out_b  (low_data_ts1755007825730)
                            );
                        end
                        for (genvar i = 0; i < 2; ++i) begin : gen_loop
                            logic [1:0] sub_in_ts1755007825730;
                            assign sub_in_ts1755007825730 = inj_in_vector_1755007825671_783[i*2 +: 2];
                            int temp_int_ts1755007825730;
                                // BEGIN: assign_pattern_lvalue_ts1755007825747
                                eight_bit_unpacked_struct_t unpacked_s;
                                logic [7:0] reg_unpacked_struct_repacked_ts1755007825747;
                                int int_var_ts1755007825747;
                                logic bit_var_ts1755007825747;
                                logic [5:0] vec_var_ts1755007825747;
                                    // BEGIN: module_packed_variables_ts1755007825756
                                    logic [31:0] data_pv_ts1755007825756 ;
                                        // BEGIN: named_block_logic_ts1755007825777
                                        logic r_internal_ts1755007825777;
                                        logic r_temp_ts1755007825777;
                                            // BEGIN: module_bitfield_concat_ts1755007825889
                                            logic [7:0] my_bitfield_ts1755007825889 ;
                                                // BEGIN: case_selector_ts1755007825968
                                                always_comb begin
                                                    case (inj_test_case_mode_1755007825680_69)
                                                        2'b00: inj_data_out_case_1755007825968_978 = inj_in_l_1755007825904_317; 
                                                        2'b01: inj_data_out_case_1755007825968_978 = inj_data1_1755007825968_632; 
                                                        2'b10: inj_data_out_case_1755007825968_978 = inj_data2_1755007825968_562; 
                                                        default: inj_data_out_case_1755007825968_978 = inj_in_vector_1755007825671_783; 
                                                    endcase
                                                end
                                                // END: case_selector_ts1755007825968

                                                // BEGIN: LintSeqNonBlockAssign_ts1755007825950
                                                always_ff @(posedge clk) begin
                                                    inj_out_g_1755007825950_76 <= bit_var_ts1755007825747;
                                                end
                                                // END: LintSeqNonBlockAssign_ts1755007825950

                                                // BEGIN: split_if_only_then_ts1755007825940
                                                always @(posedge clk) begin
                                                    if (r_temp_ts1755007825777) begin
                                                        inj_out_reg_h_1755007825940_299 <= temp_ts1755007825689;
                                                    end
                                                end
                                                // END: split_if_only_then_ts1755007825940

                                                basic_comb basic_comb_inst_1755007825934_9765 (
                                                    .out1(inj_out1_1755007825934_469),
                                                    .in1(mid_val_c_ts1755007825693),
                                                    .in2(temp_ts1755007825689)
                                                );
                                                PragmaProtectKeyBlock PragmaProtectKeyBlock_inst_1755007825919_2935 (
                                                    .enable_crypto(inj_condition_m10_1755007825699_456),
                                                    .crypto_active(inj_crypto_active_1755007825919_434)
                                                );
                                                coalesced_assign coalesced_assign_inst_1755007825904_684 (
                                                    .out(inj_out_1755007825904_519),
                                                    .in_h(inj_in_vector_1755007825671_783),
                                                    .in_l(inj_in_l_1755007825904_317)
                                                );
                                            always_comb begin
                                                if (var_m10_ts1755007825699[7]) begin
                                                    my_bitfield_ts1755007825889 = var_m10_ts1755007825699;
                                                end else begin
                                                    my_bitfield_ts1755007825889 = {var_m10_ts1755007825699[0], var_m10_ts1755007825699[7:1]};
                                                end
                                                my_bitfield_ts1755007825889[3:0] = inj_in_vector_1755007825671_783;
                                            end
                                            assign inj_output_bf_1755007825888_133 = my_bitfield_ts1755007825889;
                                            assign inj_output_bf_slice_1755007825888_515 = my_bitfield_ts1755007825889[3:0];
                                            // END: module_bitfield_concat_ts1755007825889

                                            // BEGIN: sub_inst_array_mod_ts1755007825873
                                            assign inj_out_1755007825873_310 = mid_val_c_ts1755007825693;
                                            // END: sub_inst_array_mod_ts1755007825873

                                            // BEGIN: sub_inst_array_mod_ts1755007825860
                                            assign inj_out_1755007825860_217 = mid_val_c_ts1755007825693;
                                            // END: sub_inst_array_mod_ts1755007825860

                                            Comb_Loop Comb_Loop_inst_1755007825851_3041 (
                                                .loop_in(clk),
                                                .loop_out(inj_loop_out_1755007825851_378)
                                            );
                                            // BEGIN: split_multi_nb_in_if_ts1755007825844
                                            always @(posedge clk) begin
                                                if (r_internal_ts1755007825777) begin
                                                    inj_out1_dd_1755007825844_750 <= inj_data_in_k_1755007825683_509 + var_m10_ts1755007825699;
                                                    inj_out2_dd_1755007825844_879 <= reg_unpacked_struct_repacked_ts1755007825747 - mid_val_c_ts1755007825693;
                                                end else begin
                                                    inj_out1_dd_1755007825844_750 <= inj_data_in_k_1755007825683_509 * var_m10_ts1755007825699;
                                                    inj_out2_dd_1755007825844_879 <= reg_unpacked_struct_repacked_ts1755007825747 / (mid_val_c_ts1755007825693 + 1);
                                                end
                                            end
                                            // END: split_multi_nb_in_if_ts1755007825844

                                            split_complex_nb split_complex_nb_inst_1755007825834_5188 (
                                                .i3_s(var_m10_ts1755007825699),
                                                .o1_s(inj_o1_s_1755007825834_243),
                                                .o2_s(inj_o2_s_1755007825834_982),
                                                .o3_s(inj_o3_s_1755007825834_482),
                                                .clk_s(clk),
                                                .i1_s(inj_in_b_1755007825689_56),
                                                .i2_s(reg_unpacked_struct_repacked_ts1755007825747)
                                            );
                                            PragmaDiagnosticDirective PragmaDiagnosticDirective_inst_1755007825825_3741 (
                                                .diag_output_flag(inj_diag_output_flag_1755007825825_769),
                                                .diag_input_val(int_var_ts1755007825747)
                                            );
                                            definition_used_diag_mod definition_used_diag_mod_inst_1755007825815_6675 (
                                                .in_val(inj_data_in_1755007825668_282),
                                                .out_val(inj_out_val_1755007825815_876)
                                            );
                                            mod_internal_if_test mod_internal_if_test_inst_1755007825807_8258 (
                                                .out_o(inj_out_o_1755007825807_233),
                                                .in_i(clk)
                                            );
                                            split_ifelse_chain split_ifelse_chain_inst_1755007825799_6755 (
                                                .v3_x(mid_val_c_ts1755007825693),
                                                .v1_x(reg_unpacked_struct_repacked_ts1755007825747),
                                                .out_x(inj_out_x_1755007825799_404),
                                                .c2_x(inj_enable_in_1755007825669_7),
                                                .v2_x(var_m10_ts1755007825699),
                                                .c1_x(bit_var_ts1755007825747),
                                                .c3_x(r_internal_ts1755007825777),
                                                .clk_x(clk),
                                                .v4_x(inj_in_b_1755007825689_56)
                                            );
                                            // BEGIN: sub_module_ts1755007825787
                                            assign inj_sub_out_1755007825787_338 = !r_temp_ts1755007825777;
                                            // END: sub_module_ts1755007825787

                                        always_comb begin : my_combinational_block
                                            r_temp_ts1755007825777 = inj_enable_in_1755007825669_7 & inj_sel_1755007825696_661;
                                            r_internal_ts1755007825777 = r_temp_ts1755007825777;
                                            inj_o_out_1755007825777_607 = r_internal_ts1755007825777;
                                        end
                                        // END: named_block_logic_ts1755007825777

                                        mod_case_standard mod_case_standard_inst_1755007825766_5462 (
                                            .out_status(inj_out_status_1755007825766_378),
                                            .in_cmd(inj_in_cmd_1755007825737_280)
                                        );
                                    logic [7:0] data_pa[0:1] ;
                                    always_comb begin
                                        if (inj_sel_1755007825696_661) begin
                                            data_pv_ts1755007825756[7:0] = inj_data_in_k_1755007825683_509;
                                            data_pv_ts1755007825756[15:8] = ~inj_data_in_k_1755007825683_509;
                                            data_pv_ts1755007825756[23:16] = data_pv_ts1755007825756[7:0];
                                            data_pv_ts1755007825756[31:24] = data_pv_ts1755007825756[15:8];
                                            data_pa[0] = t26_ts1755007825710[7:0];
                                            data_pa[1] = t26_ts1755007825710[15:8];
                                        end else begin
                                            data_pv_ts1755007825756 = 32'h0;
                                            data_pa[0] = 8'h0;
                                            data_pa[1] = 8'h0;
                                        end
                                    end
                                    assign inj_data_out_pv_1755007825756_779 = data_pv_ts1755007825756[3:0];
                                    assign inj_data_out_pa_1755007825756_592 = data_pa[0];
                                    // END: module_packed_variables_ts1755007825756

                                always_comb begin
                                    unpacked_s.f1 = var_m10_ts1755007825699[3:0];
                                    unpacked_s.f2 = var_m10_ts1755007825699[4];
                                    unpacked_s.f3 = var_m10_ts1755007825699[7:5];
                                    reg_unpacked_struct_repacked_ts1755007825747 = { unpacked_s.f3, unpacked_s.f2, unpacked_s.f1 };
                                    int_var_ts1755007825747 = inj_in_packed_for_conv_1755007825746_755[31:0];
                                    bit_var_ts1755007825747 = inj_in_packed_for_conv_1755007825746_755[32];
                                    vec_var_ts1755007825747 = inj_in_packed_for_conv_1755007825746_755[38:33];
                                    inj_out_unpacked_struct_repacked_1755007825745_255 = reg_unpacked_struct_repacked_ts1755007825747;
                                    inj_out_int_conv_1755007825745_924 = int_var_ts1755007825747;
                                    inj_out_bit_conv_1755007825746_998 = bit_var_ts1755007825747;
                                    inj_out_vec_conv_1755007825745_937 = vec_var_ts1755007825747;
                                end
                                // END: assign_pattern_lvalue_ts1755007825747

                                mod_case_standard mod_case_standard_inst_1755007825737_3760 (
                                    .out_status(inj_out_status_1755007825737_399),
                                    .in_cmd(inj_in_cmd_1755007825737_280)
                                );
                            ModuleBasic m_inst (
                                .a      (1'b0),
                                .b      (int'(sub_in_ts1755007825730)),
                                .out_a  (),
                                .out_b  (temp_int_ts1755007825730)
                            );
                            assign inj_data_out_1755007825729_878[i*4 +: 4] = temp_int_ts1755007825730[3:0];
                        end
                        // END: ModuleHierarchy_High_ts1755007825730

                        // BEGIN: always_multi_stmt_unhandled_ts1755007825724
                        always_comb begin
                            inj_out1_1755007825723_939 = inj_in_b_1755007825689_56;
                            inj_out2_1755007825723_864 = inj_data_in_k_1755007825683_509;
                        end
                        // END: always_multi_stmt_unhandled_ts1755007825724

                    always_comb begin
                        t1_ts1755007825710 = inj_dffcl_data_in1_1755007825663_95 + 1;
                        t2_ts1755007825710 = t1_ts1755007825710 * 2;
                        t3_ts1755007825710 = t2_ts1755007825710 - 3;
                        t4_ts1755007825710 = t3_ts1755007825710 ^ 4;
                        t5_ts1755007825710 = t4_ts1755007825710 | 5;
                        t6_ts1755007825710 = t5_ts1755007825710 & 6;
                        t7_ts1755007825710 = t6_ts1755007825710 + 7;
                        t8_ts1755007825710 = t7_ts1755007825710 - 8;
                        t9_ts1755007825710 = t8_ts1755007825710 ^ 9;
                        t10_ts1755007825710 = t9_ts1755007825710 | 10;
                        t11_ts1755007825710 = t10_ts1755007825710 & 11;
                        t12_ts1755007825710 = t11_ts1755007825710 + 12;
                        t13_ts1755007825710 = t12_ts1755007825710 - 13;
                        t14_ts1755007825710 = t13_ts1755007825710 ^ 14;
                        t15_ts1755007825710 = t14_ts1755007825710 | 15;
                        t16_ts1755007825710 = t15_ts1755007825710 + 16;
                        t17_ts1755007825710 = t16_ts1755007825710 * 17;
                        t18_ts1755007825710 = t17_ts1755007825710 - 18;
                        t19_ts1755007825710 = t18_ts1755007825710 ^ 19;
                        t20_ts1755007825710 = t19_ts1755007825710 | 20;
                        t21_ts1755007825710 = t20_ts1755007825710 + 1;
                        t22_ts1755007825710 = t21_ts1755007825710 * 2;
                        t23_ts1755007825710 = t22_ts1755007825710 - 3;
                        t24_ts1755007825710 = t23_ts1755007825710 ^ 4;
                        t25_ts1755007825710 = t24_ts1755007825710 | 5;
                        t26_ts1755007825710 = t25_ts1755007825710 & 6;
                        t27_ts1755007825710 = t26_ts1755007825710 + 7;
                        t28_ts1755007825710 = t27_ts1755007825710 - 8;
                        t29_ts1755007825710 = t28_ts1755007825710 ^ 9;
                        t30_ts1755007825710 = t29_ts1755007825710 | 10;
                        t31_ts1755007825710 = t30_ts1755007825710 & 11;
                        t32_ts1755007825710 = t31_ts1755007825710 + 12;
                        t33_ts1755007825710 = t32_ts1755007825710 - 13;
                        t34_ts1755007825710 = t33_ts1755007825710 ^ 14;
                        t35_ts1755007825710 = t34_ts1755007825710 | 15;
                        t36_ts1755007825710 = t35_ts1755007825710 + 16;
                        t37_ts1755007825710 = t36_ts1755007825710 * 17;
                        t38_ts1755007825710 = t37_ts1755007825710 - 18;
                        t39_ts1755007825710 = t38_ts1755007825710 ^ 19;
                        t40_ts1755007825710 = t39_ts1755007825710 | 20;
                        inj_dcac_end_val_1755007825709_193 = t40_ts1755007825710;
                    end
                    // END: deep_comb_assign_chain_ts1755007825717

                begin
                temp_ts1755007825706 = val1 + val2;
                add_and_subtract = temp_ts1755007825706 - 1;
                end
                endfunction
                always_comb begin
                inj_out_func_result_1755007825706_323 = add_and_subtract(inj_param_in_1755007825676_185, inj_in_func_b_1755007825706_819);
                end
                // END: module_function_ts1755007825706

                // BEGIN: split_input_only_var_ts1755007825703
                always @(posedge clk) begin
                    if (inj_data_in_1755007825669_956) begin
                        inj_data_out_k_1755007825702_324 <= var_m10_ts1755007825699;
                    end
                end
                // END: split_input_only_var_ts1755007825703

            always_comb begin
                var_m10_ts1755007825699 = inj_in_b_1755007825689_56;
                inj_out_val_m10_1755007825699_298 = inj_condition_m10_1755007825699_456 ? var_m10_ts1755007825699 : var_m10_ts1755007825699;
                var_m10_ts1755007825699++;
            end
            // END: unsupported_cond_expr_ts1755007825699

            // BEGIN: multiplexer_2to1_ts1755007825696
            assign inj_result_1755007825696_40 = inj_sel_1755007825696_661 ? inj_enable_in_1755007825669_7 : inj_data_in_1755007825669_956;
            // END: multiplexer_2to1_ts1755007825696

        always @(posedge clk) begin
            mid_val_c_ts1755007825693 <= inj_in_b_1755007825689_56 + 1;
            inj_out_val_c_1755007825693_459 <= mid_val_c_ts1755007825693 * 2;
        end
        // END: split_seq_dependency_ts1755007825693

    always_comb begin
        temp_ts1755007825689 = inj_data_in_k_1755007825683_509 + inj_in_b_1755007825689_56;
    end
    assign inj_out_ops_1755007825689_880 = (inj_data_in_k_1755007825683_509 & inj_in_b_1755007825689_56) | (inj_data_in_k_1755007825683_509 ^ inj_in_b_1755007825689_56);
    assign inj_out_cmp_1755007825689_313 = (inj_data_in_k_1755007825683_509 == inj_in_b_1755007825689_56);
    // END: Module_BasicSyntax_ts1755007825689

    // BEGIN: mod_basic_bind_ts1755007825686
    assign inj_out1_bind_def_1755007825686_491 = ~inj_enable_in_1755007825669_7;
    // END: mod_basic_bind_ts1755007825686

    split_input_only_var split_input_only_var_inst_1755007825683_1737 (
        .data_in_k(inj_data_in_k_1755007825683_509),
        .data_out_k(inj_data_out_k_1755007825683_90),
        .clk_k(clk),
        .control_signal_k(inj_data_in_1755007825669_956)
    );
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
assign inj_test_case_result_1755007825680_285 = (inj_test_case_mode_1755007825680_69 == 2'b01) ? 4'h5 : 4'hA;
    // END: PragmaSyntaxVariety_ts1755007825681

    mod_module_attrs mod_module_attrs_inst_1755007825678_6341 (
        .i_in(inj_param_in_1755007825676_185),
        .o_out(inj_o_out_1755007825678_977)
    );
    assign inj_param_out_1755007825676_872 = inj_param_in_1755007825676_185;
    // END: module_with_params_ts1755007825676

    assign inj_data_b_1755007825674_312 = ~reset;
    // END: simple_logic_a_ts1755007825674

    always_comb begin
        inj_out_res_1755007825672_833 = 1'b0;
        casez (inj_in_val_1755007825672_814)
            3'b1??: inj_out_res_1755007825672_833 = 1'b1;
            3'b0z?: inj_out_res_1755007825672_833 = 1'b0;
            default: inj_out_res_1755007825672_833 = 1'b1;
        endcase
    end
    // END: casez_xz_ts1755007825673

    combinatorial_logic combinatorial_logic_inst_1755007825671_6578 (
        .in_vector(inj_in_vector_1755007825671_783),
        .out_single(inj_out_single_1755007825671_98)
    );
    always_ff @(posedge clk or negedge reset) begin
        if (!reset) begin
            inj_data_out_1755007825669_3 <= 1'b0; 
        end else if (inj_enable_in_1755007825669_7) begin
            inj_data_out_1755007825669_3 <= inj_data_in_1755007825669_956; 
        end
    end
    // END: sequential_register_ts1755007825669

    always_comb begin : my_named_block
        inj_data_out_1755007825668_822 = inj_data_in_1755007825668_282;
    end
    // END: mod_named_begin_ts1755007825668

    assign inj_out_1755007825667_872 = (inj_in1_1755007825667_1 + inj_in2_1755007825667_769) * inj_in3_1755007825667_304 > inj_in4_1755007825667_805 - inj_in5_1755007825667_889;
    // END: arith_comp_ops_ts1755007825667

    always_ff @(posedge clk or negedge reset) begin
    if (!reset) begin
        inj_dffcl_data_out_1755007825663_808 <= 16'h0000;
    end else begin
        case (inj_dffcl_ctrl_mode_1755007825663_431)
            4'd0: inj_dffcl_data_out_1755007825663_808 <= inj_dffcl_data_in1_1755007825663_95 + inj_dffcl_data_in2_1755007825663_582;
            4'd1: begin
                if (inj_dffcl_data_in1_1755007825663_95 > inj_dffcl_data_in2_1755007825663_582) begin
                    case (inj_dffcl_ctrl_mode_1755007825663_431[1:0])
                        2'b00: inj_dffcl_data_out_1755007825663_808 <= inj_dffcl_data_in1_1755007825663_95 - inj_dffcl_data_in2_1755007825663_582;
                        2'b01: inj_dffcl_data_out_1755007825663_808 <= inj_dffcl_data_in1_1755007825663_95 & inj_dffcl_data_in2_1755007825663_582;
                        default: inj_dffcl_data_out_1755007825663_808 <= inj_dffcl_data_in1_1755007825663_95 | inj_dffcl_data_in2_1755007825663_582;
                    endcase
                end else begin
                    case (inj_dffcl_ctrl_mode_1755007825663_431[1:0])
                        2'b00: inj_dffcl_data_out_1755007825663_808 <= inj_dffcl_data_in2_1755007825663_582 - inj_dffcl_data_in1_1755007825663_95;
                        2'b01: inj_dffcl_data_out_1755007825663_808 <= inj_dffcl_data_in1_1755007825663_95 ^ inj_dffcl_data_in2_1755007825663_582;
                        default: inj_dffcl_data_out_1755007825663_808 <= ~inj_dffcl_data_in1_1755007825663_95;
                    endcase
                end
            end
            4'd2: begin
                casez (inj_dffcl_data_in1_1755007825663_95[15:13])
                    3'b000: inj_dffcl_data_out_1755007825663_808 <= inj_dffcl_data_in2_1755007825663_582;
                    3'b001: inj_dffcl_data_out_1755007825663_808 <= ~inj_dffcl_data_in2_1755007825663_582;
                    3'b01?: begin
                        if (inj_dffcl_data_in2_1755007825663_582[0]) inj_dffcl_data_out_1755007825663_808 <= inj_dffcl_data_in1_1755007825663_95 << 1;
                        else inj_dffcl_data_out_1755007825663_808 <= inj_dffcl_data_in1_1755007825663_95 >> 1;
                    end
                    3'b1??: begin
                        if (inj_dffcl_ctrl_mode_1755007825663_431[0]) inj_dffcl_data_out_1755007825663_808 <= inj_dffcl_data_in1_1755007825663_95 + 1;
                        else inj_dffcl_data_out_1755007825663_808 <= inj_dffcl_data_in1_1755007825663_95 - 1;
                    end
                    default: inj_dffcl_data_out_1755007825663_808 <= 16'hAAAA;
                endcase
            end
            default: begin
                if (inj_dffcl_ctrl_mode_1755007825663_431[2]) inj_dffcl_data_out_1755007825663_808 <= inj_dffcl_data_in1_1755007825663_95;
                else inj_dffcl_data_out_1755007825663_808 <= inj_dffcl_data_in2_1755007825663_582;
            end
        endcase
    end
    end
    // END: deep_ff_control_logic_ts1755007825666
endmodule

