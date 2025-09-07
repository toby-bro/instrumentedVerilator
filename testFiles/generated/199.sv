module CaseEq (
    output wire match_x_neq,
    output wire match_z_eq,
    inout wire [3:0] data_io
);
    assign match_z_eq = (data_io === 4'b101z);
    assign match_x_neq = (data_io !== 4'b1x0x);
endmodule

module CombinationalLogicImplicit (
    input logic [3:0] a,
    input logic [3:0] b,
    output logic [3:0] sum
);
    always @* begin
        sum = a + b;
    end
endmodule

module CoverageHelper (
    input bit in_h,
    output logic out_h
);
    assign out_h = in_h;
endmodule

module LintSensitiveList (
    input logic in_p,
    input logic in_q,
    output logic out_r
);
    always_comb begin
        out_r = in_p | in_q;
    end
endmodule

module Module_ConfigKeywords (
    input bit cfg_in,
    output bit cfg_out
);
    assign cfg_out = cfg_in;
endmodule

module Module_IfNoneParam (
    input int in_port,
    output int out_port
);
    assign out_port = in_port;
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

module ShiftOperations (
    input logic [7:0] data,
    input logic [2:0] shift_val,
    output logic [7:0] left_shift_log,
    output logic [7:0] right_shift_arith,
    output logic [7:0] right_shift_log
);
    assign left_shift_log = data << shift_val;
    assign right_shift_log = data >> shift_val;
    assign right_shift_arith = $signed(data) >>> shift_val;
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

module casez_xz (
    input logic [2:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            3'b1??: out_res = 1'b1;
            3'b0z?: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module comb_conditional (
    input bit [7:0] data1,
    input bit [7:0] data2,
    input bit sel,
    output bit [7:0] result1,
    output bit [7:0] result2
);
    always @* begin
        if (sel) begin
            result1 = data1;
            result2 = data1;
        end else begin
            result1 = data2;
            result2 = data2;
        end
    end
endmodule

module func_macro_defaults (
    input logic en,
    output logic [7:0] default_out
);
    `define DEFAULT_CONST       8'hAA
    `define CALC(val, def=`DEFAULT_CONST) ((val) | (def))
    localparam logic [7:0] P_WITH_DEF     = `CALC(8'h0F);
    localparam logic [7:0] P_OVERRIDE_DEF = `CALC(8'hF0, 8'h11);
    assign default_out = en ? P_WITH_DEF : P_OVERRIDE_DEF;
endmodule

module mod_event_posedge (
    input wire clk,
    input wire data_in,
    output reg data_out
);
    always @(posedge clk) begin
        data_out <= data_in;
    end
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

module mod_if_else_simple (
    input bit [3:0] in_data,
    output bit [3:0] out_result
);
always_comb begin
    if (in_data > 8) begin
        out_result = in_data + 1;
    end else begin
        out_result = in_data - 1;
    end
end
endmodule

module module_concat_if (
    input wire [3:0] in_a,
    input wire [3:0] in_b,
    input wire [7:0] in_c,
    input wire in_cond_if,
    output logic [15:0] out_concat,
    output logic [7:0] out_if_else
);
    always_comb begin
    out_concat = {in_a, in_b, in_c};
    if (in_cond_if) begin
        out_if_else = in_c;
    end else begin
        out_if_else = {in_a, in_b};
    end
    end
endmodule

module nested_types_mod (
    input logic [31:0] nested_in,
    output logic [7:0] inner_field_o
);
    typedef struct packed {
        logic [7:0] inner_field;
        logic [7:0] padding;
    } inner_struct_t;
    typedef union packed {
        logic [31:0] full_word;
        struct packed {
            logic [15:0] unused;
            inner_struct_t inner_data;
        } outer_fields;
    } outer_union_t;
    outer_union_t nested_var;
    always_comb begin
        nested_var.full_word = nested_in;
    end
    assign inner_field_o = nested_var.outer_fields.inner_data.inner_field;
endmodule

module rand_case_mod (
    input logic [2:0] selector,
    output logic [3:0] result_out
);
    always_comb begin
        case (selector)
            0: result_out = 4'h0;
            1: result_out = 4'h1;
            2: result_out = 4'hA;
            default: result_out = 4'hF;
        endcase
    end
endmodule

module split_diff_vars_branches (
    input logic clk_z,
    input logic condition_z,
    input logic [7:0] in1_z,
    input logic [7:0] in2_z,
    output logic [7:0] out1_z,
    output logic [7:0] out2_z
);
    always @(posedge clk_z) begin
        if (condition_z) begin
            out1_z <= in1_z;
        end else begin
            out2_z <= in2_z;
        end
    end
endmodule

module split_vector_assign (
    input logic clk_y,
    input logic condition_y,
    input logic [7:0] in_val_y,
    output logic [7:0] out_vec_y
);
    always @(posedge clk_y) begin
        if (condition_y) begin
            out_vec_y[3:0] <= in_val_y[3:0];
            out_vec_y[7:4] <= in_val_y[7:4] + 1;
        end else begin
            out_vec_y <= 8'hFF;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_a_1755007819650_834,
    input logic [3:0] inj_b_1755007819650_898,
    input wire [1:0] inj_byte_idx_1755007819724_379,
    input logic [7:0] inj_d1_w_1755007819652_190,
    input logic [7:0] inj_d2_w_1755007819652_269,
    input logic [7:0] inj_d3_w_1755007819652_537,
    input bit [7:0] inj_data1_1755007819654_884,
    input bit [7:0] inj_data2_1755007819654_640,
    input wire [3:0] inj_in_a_1755007819731_536,
    input wire [3:0] inj_in_b_1755007819731_436,
    input bit [3:0] inj_in_data_1755007819650_11,
    input wire [7:0] inj_in_func_a_1755007819651_545,
    input wire [7:0] inj_in_func_b_1755007819651_881,
    input logic inj_in_p_1755007819650_437,
    input int inj_in_port_1755007819672_201,
    input logic inj_in_q_1755007819650_18,
    input logic [7:0] inj_in_wide_1755007819650_535,
    input logic [31:0] inj_nested_in_1755007819669_926,
    input bit inj_sel_1755007819654_480,
    input logic [1:0] inj_sel_w_1755007819652_659,
    input logic [2:0] inj_shift_val_1755007819655_220,
    input logic [63:0] inj_wide_a_1755007819663_871,
    input logic [63:0] inj_wide_b_1755007819663_424,
    input logic [63:0] inj_wide_c_1755007819664_438,
    input wire [31:0] inj_wide_data_1755007819724_420,
    input wire reset,
    output logic inj_comb_out_1755007819786_719,
    output reg inj_data_out_1755007819660_893,
    output logic inj_data_ref_out_1755007819768_506,
    output logic [7:0] inj_default_out_1755007819719_211,
    output logic inj_dout_1755007819708_210,
    output wire inj_fs_out_1755007819651_857,
    output logic [7:0] inj_inner_field_o_1755007819669_321,
    output logic [7:0] inj_inner_field_o_1755007819700_240,
    output logic [4:0] inj_internal_out_1755007819653_170,
    output logic [7:0] inj_left_shift_log_1755007819655_684,
    output wire inj_match_x_neq_1755007819680_574,
    output wire inj_match_z_eq_1755007819680_331,
    output logic [7:0] inj_out1_1755007819674_845,
    output logic [7:0] inj_out1_z_1755007819688_741,
    output logic [7:0] inj_out2_z_1755007819688_596,
    output logic inj_out_a_1755007819684_715,
    output int inj_out_b_1755007819684_998,
    output logic inj_out_c_1755007819661_218,
    output logic [15:0] inj_out_concat_1755007819731_763,
    output logic [7:0] inj_out_func_result_1755007819651_992,
    output logic inj_out_h_1755007819746_286,
    output logic [7:0] inj_out_if_else_1755007819731_707,
    output logic [3:0] inj_out_narrow_1755007819650_613,
    output int inj_out_port_1755007819672_197,
    output logic inj_out_r_1755007819650_872,
    output logic [7:0] inj_out_reg_t_1755007819753_35,
    output reg inj_out_res_1755007819760_828,
    output reg inj_out_res_1755007819777_655,
    output bit [3:0] inj_out_result_1755007819650_436,
    output bit inj_out_tc_1755007819693_863,
    output logic [7:0] inj_out_vec_y_1755007819713_380,
    output logic [7:0] inj_out_w_1755007819652_189,
    output logic inj_out_wire_1755007819697_114,
    output logic inj_out_wire_1755007819795_569,
    output logic [7:0] inj_out_x_1755007819677_586,
    output wire inj_p_out_1755007819657_198,
    output logic inj_q_1755007819737_153,
    output reg [7:0] inj_q_out_1755007819667_132,
    output bit [7:0] inj_result1_1755007819654_958,
    output bit [7:0] inj_result2_1755007819654_216,
    output logic [3:0] inj_result_out_1755007819659_588,
    output logic [7:0] inj_right_shift_arith_1755007819655_516,
    output logic [7:0] inj_right_shift_log_1755007819655_338,
    output reg [7:0] inj_selected_byte_1755007819724_465,
    output logic inj_seq_out_1755007819786_702,
    output logic inj_status_out_1755007819768_486,
    output logic [3:0] inj_sum_1755007819650_139,
    output logic [3:0] inj_test_case_result_1755007819656_97,
    output logic [63:0] inj_wide_out_1755007819663_270,
    output logic [7:0] inj_x_aa_1755007819704_571,
    output logic [7:0] inj_y_aa_1755007819704_321,
    output logic [7:0] inj_z_aa_1755007819704_903,
    inout wire inj_data_inout_1755007819768_539,
    inout wire [3:0] inj_data_io_1755007819680_615
);
    // BEGIN: LintImplicitWidth_ts1755007819650
    // BEGIN: module_function_ts1755007819651
    function automatic [7:0] add_and_subtract;
    input [7:0] val1;
    input [7:0] val2;
    reg [7:0] temp_ts1755007819651;
        // BEGIN: explicit_non_ansi_decl_module_ts1755007819657
        input logic inj_in_q_1755007819650_18_ts1755007819657;
        output wire inj_p_out_1755007819657_198_ts1755007819657;
            // BEGIN: basic_assign_if_ts1755007819662
            logic intermediate_wire_ts1755007819662;
                // BEGIN: basic_comb_ts1755007819674
                ;
                logic [7:0] temp_wire_ts1755007819674;
                    // BEGIN: ModuleBasic_ts1755007819684
                    parameter int P1  = 10;
                    localparam int LP1 = 20;
                    logic c_ts1755007819684;
                    int   d_ts1755007819684;
                    always_comb begin
                        logic temp_v_ts1755007819684;
                            // BEGIN: MixedLogic_ts1755007819786
                            logic seq_reg_ts1755007819786;
                            logic comb_intermediate_ts1755007819786;
                                // BEGIN: net_var_conn_child_ts1755007819795
                                assign inj_out_wire_1755007819795_569 = intermediate_wire_ts1755007819662;
                                // END: net_var_conn_child_ts1755007819795

                            always @(posedge clk or negedge reset) begin
                                if (!reset) begin
                                    seq_reg_ts1755007819786 <= 1'b0;
                                end else begin
                                    seq_reg_ts1755007819786 <= inj_in_q_1755007819650_18;
                                end
                            end
                            assign inj_seq_out_1755007819786_702 = seq_reg_ts1755007819786;
                            always @(seq_reg_ts1755007819786 or inj_in_p_1755007819650_437 or c_ts1755007819684) begin
                                comb_intermediate_ts1755007819786 = (seq_reg_ts1755007819786 & inj_in_p_1755007819650_437) | (~seq_reg_ts1755007819786 & c_ts1755007819684);
                            end
                            assign inj_comb_out_1755007819786_719 = comb_intermediate_ts1755007819786;
                            // END: MixedLogic_ts1755007819786

                            // BEGIN: case_empty_statement_ts1755007819777
                            always_comb begin
                                inj_out_res_1755007819777_655 = 1'b0;
                                case (inj_sel_w_1755007819652_659)
                                    2'b00: inj_out_res_1755007819777_655 = 1'b1;
                                    2'b01: ;
                                    2'b10: inj_out_res_1755007819777_655 = 1'b0;
                                    default: inj_out_res_1755007819777_655 = 1'b1;
                                endcase
                            end
                            // END: case_empty_statement_ts1755007819777

                            // BEGIN: ansi_directions_ts1755007819769
                            logic internal_data = 1'b0;
                            assign inj_data_inout_1755007819768_539 = internal_data;
                            always_comb begin
                                inj_data_ref_out_1755007819768_506 = intermediate_wire_ts1755007819662;
                                internal_data = inj_data_inout_1755007819768_539;
                                inj_status_out_1755007819768_486 = internal_data | inj_in_p_1755007819650_437;
                            end
                            // END: ansi_directions_ts1755007819769

                            casez_xz casez_xz_inst_1755007819760_9012 (
                                .in_val(inj_shift_val_1755007819655_220),
                                .out_res(inj_out_res_1755007819760_828)
                            );
                            // BEGIN: split_if_empty_branches_ts1755007819753
                            always @(posedge clk) begin
                                if (temp_v_ts1755007819684) begin
                                end else begin
                                end
                            end
                            // END: split_if_empty_branches_ts1755007819753

                            CoverageHelper CoverageHelper_inst_1755007819746_6217 (
                                .out_h(inj_out_h_1755007819746_286),
                                .in_h(inj_sel_1755007819654_480)
                            );
                            // BEGIN: basic_d_flipflop_ts1755007819738
                            always_ff @(posedge clk) begin
                                inj_q_1755007819737_153 <= c_ts1755007819684;
                            end
                            // END: basic_d_flipflop_ts1755007819738

                            module_concat_if module_concat_if_inst_1755007819731_7785 (
                                .in_a(inj_in_a_1755007819731_536),
                                .in_b(inj_in_b_1755007819731_436),
                                .in_c(inj_in_func_b_1755007819651_881),
                                .in_cond_if(inj_p_out_1755007819657_198_ts1755007819657),
                                .out_concat(inj_out_concat_1755007819731_763),
                                .out_if_else(inj_out_if_else_1755007819731_707)
                            );
                            // BEGIN: Bit_Manip_ts1755007819725
                            always_comb begin
                                case (inj_byte_idx_1755007819724_379)
                                    2'b00: inj_selected_byte_1755007819724_465 = inj_wide_data_1755007819724_420[7:0];
                                    2'b01: inj_selected_byte_1755007819724_465 = inj_wide_data_1755007819724_420[15:8];
                                    2'b10: inj_selected_byte_1755007819724_465 = inj_wide_data_1755007819724_420[23:16];
                                    default: inj_selected_byte_1755007819724_465 = inj_wide_data_1755007819724_420[31:24];
                                endcase
                            end
                            // END: Bit_Manip_ts1755007819725

                            func_macro_defaults func_macro_defaults_inst_1755007819719_5571 (
                                .default_out(inj_default_out_1755007819719_211),
                                .en(intermediate_wire_ts1755007819662)
                            );
                            split_vector_assign split_vector_assign_inst_1755007819713_7395 (
                                .condition_y(inj_in_q_1755007819650_18),
                                .in_val_y(inj_d1_w_1755007819652_190),
                                .out_vec_y(inj_out_vec_y_1755007819713_380),
                                .clk_y(clk)
                            );
                            // BEGIN: ModRegister_ts1755007819708
                            always @* begin
                                inj_dout_1755007819708_210 = temp_v_ts1755007819684;
                            end
                            // END: ModRegister_ts1755007819708

                            // BEGIN: split_combo_blocking_ts1755007819704
                            always @(*) begin
                                inj_x_aa_1755007819704_571 = inj_d1_w_1755007819652_190 + inj_d2_w_1755007819652_269;
                                inj_y_aa_1755007819704_321 = inj_x_aa_1755007819704_571 - inj_in_wide_1755007819650_535;
                                inj_z_aa_1755007819704_903 = inj_d1_w_1755007819652_190 * inj_in_wide_1755007819650_535;
                            end
                            // END: split_combo_blocking_ts1755007819704

                            // BEGIN: nested_types_mod_ts1755007819700
                            typedef struct packed {
                                logic [7:0] inner_field_ts1755007819700;
                                logic [7:0] padding_ts1755007819700;
                            } inner_struct_t;
                            typedef union packed {
                                logic [31:0] full_word_ts1755007819700;
                                struct packed {
                                    logic [15:0] unused_ts1755007819700;
                                    inner_struct_t inner_data;
                                } outer_fields;
                            } outer_union_t;
                            outer_union_t nested_var;
                            always_comb begin
                                nested_var.full_word_ts1755007819700 = inj_nested_in_1755007819669_926;
                            end
                            assign inj_inner_field_o_1755007819700_240 = nested_var.outer_fields.inner_data.inner_field_ts1755007819700;
                            // END: nested_types_mod_ts1755007819700

                            // BEGIN: net_var_conn_child_ts1755007819697
                            assign inj_out_wire_1755007819697_114 = temp_v_ts1755007819684;
                            // END: net_var_conn_child_ts1755007819697

                            // BEGIN: TopConfigExample_ts1755007819693
                            Module_ConfigKeywords i_cfg (.cfg_in(inj_sel_1755007819654_480), .cfg_out(inj_out_tc_1755007819693_863));
                            // END: TopConfigExample_ts1755007819693

                            split_diff_vars_branches split_diff_vars_branches_inst_1755007819688_7596 (
                                .out1_z(inj_out1_z_1755007819688_741),
                                .out2_z(inj_out2_z_1755007819688_596),
                                .clk_z(clk),
                                .condition_z(temp_v_ts1755007819684),
                                .in1_z(inj_d1_w_1755007819652_190),
                                .in2_z(inj_in_wide_1755007819650_535)
                            );
                        temp_v_ts1755007819684 = d_ts1755007819684;
                        c_ts1755007819684      = temp_v_ts1755007819684;
                    end
                    assign inj_out_a_1755007819684_715 = inj_in_q_1755007819650_18_ts1755007819657;
                    assign d_ts1755007819684     = inj_in_port_1755007819672_201;
                    assign inj_out_b_1755007819684_998 = d_ts1755007819684 + P1 + LP1;
                    // END: ModuleBasic_ts1755007819684

                    CaseEq CaseEq_inst_1755007819680_364 (
                        .match_x_neq(inj_match_x_neq_1755007819680_574),
                        .match_z_eq(inj_match_z_eq_1755007819680_331),
                        .data_io(inj_data_io_1755007819680_615)
                    );
                    // BEGIN: split_ifelse_chain_ts1755007819677
                    always @(posedge clk) begin
                        if (inj_in_q_1755007819650_18_ts1755007819657) begin
                            inj_out_x_1755007819677_586 <= temp_wire_ts1755007819674;
                        end else if (inj_in_q_1755007819650_18) begin
                            inj_out_x_1755007819677_586 <= inj_in_wide_1755007819650_535;
                        end else if (intermediate_wire_ts1755007819662) begin
                            inj_out_x_1755007819677_586 <= inj_d2_w_1755007819652_269;
                        end else begin
                            inj_out_x_1755007819677_586 <= inj_d3_w_1755007819652_537;
                        end
                    end
                    // END: split_ifelse_chain_ts1755007819677

                assign temp_wire_ts1755007819674 = inj_d2_w_1755007819652_269 + inj_d1_w_1755007819652_190;
                always_comb begin
                    inj_out1_1755007819674_845 = temp_wire_ts1755007819674;
                end
                // END: basic_comb_ts1755007819674

                Module_IfNoneParam Module_IfNoneParam_inst_1755007819672_9148 (
                    .in_port(inj_in_port_1755007819672_201),
                    .out_port(inj_out_port_1755007819672_197)
                );
                nested_types_mod nested_types_mod_inst_1755007819669_2384 (
                    .nested_in(inj_nested_in_1755007819669_926),
                    .inner_field_o(inj_inner_field_o_1755007819669_321)
                );
                // BEGIN: Seq_DFF_ts1755007819667
                always_ff @(posedge clk or posedge reset) begin
                    if (reset) begin
                        inj_q_out_1755007819667_132 <= 8'b0;
                    end else begin
                        inj_q_out_1755007819667_132 <= inj_in_func_b_1755007819651_881;
                    end
                end
                // END: Seq_DFF_ts1755007819667

                // BEGIN: wide_ops_deep_ts1755007819664
                assign inj_wide_out_1755007819663_270 = (((inj_wide_a_1755007819663_871 + inj_wide_b_1755007819663_424) ^ inj_wide_c_1755007819664_438) & (~inj_wide_a_1755007819663_871 | inj_wide_b_1755007819663_424)) + (inj_wide_c_1755007819664_438 >>> 5);
                // END: wide_ops_deep_ts1755007819664

            assign intermediate_wire_ts1755007819662 = inj_in_q_1755007819650_18_ts1755007819657 & inj_in_q_1755007819650_18;
            always_comb begin
                if (intermediate_wire_ts1755007819662) begin
                    inj_out_c_1755007819661_218 = 1'b1;
                end else begin
                    inj_out_c_1755007819661_218 = 1'b0;
                end
            end
            // END: basic_assign_if_ts1755007819662

            mod_event_posedge mod_event_posedge_inst_1755007819660_7729 (
                .clk(clk),
                .data_in(reset),
                .data_out(inj_data_out_1755007819660_893)
            );
            rand_case_mod rand_case_mod_inst_1755007819659_6180 (
                .selector(inj_shift_val_1755007819655_220),
                .result_out(inj_result_out_1755007819659_588)
            );
        assign inj_p_out_1755007819657_198_ts1755007819657 = inj_in_q_1755007819650_18_ts1755007819657;
        // END: explicit_non_ansi_decl_module_ts1755007819657

        PragmaSyntaxVariety PragmaSyntaxVariety_inst_1755007819656_4506 (
            .test_case_mode(inj_sel_w_1755007819652_659),
            .test_case_result(inj_test_case_result_1755007819656_97)
        );
        ShiftOperations ShiftOperations_inst_1755007819655_548 (
            .right_shift_log(inj_right_shift_log_1755007819655_338),
            .data(inj_in_wide_1755007819650_535),
            .shift_val(inj_shift_val_1755007819655_220),
            .left_shift_log(inj_left_shift_log_1755007819655_684),
            .right_shift_arith(inj_right_shift_arith_1755007819655_516)
        );
        comb_conditional comb_conditional_inst_1755007819654_7707 (
            .result1(inj_result1_1755007819654_958),
            .result2(inj_result2_1755007819654_216),
            .data1(inj_data1_1755007819654_884),
            .data2(inj_data2_1755007819654_640),
            .sel(inj_sel_1755007819654_480)
        );
        case_full_simple_mod case_full_simple_mod_inst_1755007819653_6033 (
            .case_expr(inj_sel_w_1755007819652_659),
            .internal_out(inj_internal_out_1755007819653_170)
        );
        // BEGIN: split_case_ts1755007819652
        always @(posedge clk) begin
            case (inj_sel_w_1755007819652_659)
                2'b00: inj_out_w_1755007819652_189 <= inj_in_wide_1755007819650_535;
                2'b01: inj_out_w_1755007819652_189 <= inj_d1_w_1755007819652_190;
                2'b10: inj_out_w_1755007819652_189 <= inj_d2_w_1755007819652_269;
                default: inj_out_w_1755007819652_189 <= inj_d3_w_1755007819652_537;
            endcase
        end
        // END: split_case_ts1755007819652

        mod_fixup_syntax_user mod_fixup_syntax_user_inst_1755007819651_9311 (
            .fs_in(inj_in_p_1755007819650_437),
            .fs_out(inj_fs_out_1755007819651_857)
        );
    begin
    temp_ts1755007819651 = val1 + val2;
    add_and_subtract = temp_ts1755007819651 - 1;
    end
    endfunction
    always_comb begin
    inj_out_func_result_1755007819651_992 = add_and_subtract(inj_in_func_a_1755007819651_545, inj_in_func_b_1755007819651_881);
    end
    // END: module_function_ts1755007819651

    assign inj_out_narrow_1755007819650_613 = inj_in_wide_1755007819650_535;
    // END: LintImplicitWidth_ts1755007819650

    CombinationalLogicImplicit CombinationalLogicImplicit_inst_1755007819650_2555 (
        .b(inj_b_1755007819650_898),
        .sum(inj_sum_1755007819650_139),
        .a(inj_a_1755007819650_834)
    );
    LintSensitiveList LintSensitiveList_inst_1755007819650_5393 (
        .out_r(inj_out_r_1755007819650_872),
        .in_p(inj_in_p_1755007819650_437),
        .in_q(inj_in_q_1755007819650_18)
    );
    mod_if_else_simple mod_if_else_simple_inst_1755007819650_1778 (
        .in_data(inj_in_data_1755007819650_11),
        .out_result(inj_out_result_1755007819650_436)
    );
endmodule

