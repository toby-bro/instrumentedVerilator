module CaseStatementConditions (
    input wire [3:0] data_c,
    input wire [1:0] selector,
    output logic [3:0] out_case_case,
    output logic [3:0] out_case_casex,
    output logic [3:0] out_case_casez
);
    always_comb begin
        case (selector)
            2'b00: out_case_case = data_c;
            2'b01: out_case_case = data_c + 1;
            2'b10: out_case_case = data_c + 2;
            default: out_case_case = 4'bxxxx;
        endcase
        casez (selector)
            2'b0?: out_case_casez = data_c + 10;
            2'b1?: out_case_casez = data_c + 20;
            default: out_case_casez = 4'bzzzz;
        endcase
        casex (selector)
            2'b0?: out_case_casex = data_c - 1;
            2'b1?: out_case_casex = data_c - 2;
            default: out_case_casex = 4'bxxxx;
        endcase
    end
endmodule

module LintSeqNonBlockAssign (
    input logic clk,
    input logic in_f,
    output logic out_g
);
    always_ff @(posedge clk) begin
        out_g <= in_f;
    end
endmodule

module Mod_TernaryLogic (
    input wire [7:0] in_a,
    input wire [7:0] in_b,
    input wire in_bit,
    input wire [7:0] in_c,
    input wire in_cond,
    input wire in_cond_neq_lhs,
    input wire in_cond_neq_rhs,
    input wire in_cond_not,
    input wire [7:0] in_not_else,
    input wire [7:0] in_not_then,
    output logic out_eq,
    output logic out_eq_concat,
    output logic out_gt,
    output logic out_gte,
    output logic out_lt,
    output logic out_lte,
    output logic out_neq,
    output logic out_not_eq,
    output logic out_not_neq,
    output logic out_ternary,
    output logic out_ternary_1bit_0else,
    output logic out_ternary_1bit_0then,
    output logic out_ternary_1bit_1else,
    output logic out_ternary_1bit_1then,
    output logic out_ternary_const_cond_false,
    output logic out_ternary_const_cond_true,
    output logic [7:0] out_ternary_dec,
    output logic [7:0] out_ternary_inc,
    output logic [7:0] out_ternary_pulled_nots,
    output logic out_ternary_swapped_cond,
    output logic out_ternary_swapped_neq_cond
);
    parameter [7:0] CONST_ONE_8 = 8'h01;
    parameter [0:0] CONST_ZERO_1 = 1'b0;
    parameter [0:0] CONST_ONE_1 = 1'b1;
    logic [7:0] intermediate_const_concat_comp;
    logic [15:0] intermediate_concat_comp_src;
    always_comb begin
        out_eq = (in_a == in_b);
        out_neq = (in_a != in_b);
        out_gt = (in_a > in_b);
        out_lt = (in_a < in_b);
        out_gte = (in_a >= in_b);
        out_lte = (in_a <= in_b);
        out_not_eq = !(in_a == in_b);
        out_not_neq = !(in_a != in_b);
        intermediate_const_concat_comp = 8'hAA;
        intermediate_concat_comp_src = {in_a, in_b};
        out_eq_concat = (intermediate_const_concat_comp == intermediate_concat_comp_src[7:0]);
        out_ternary = in_cond ? in_a[0] : in_b[0];
        out_ternary_const_cond_true = 1'b1 ? in_a[0] : in_b[0];
        out_ternary_const_cond_false = 1'b0 ? in_a[0] : in_b[0];
        out_ternary_swapped_cond = !in_cond_not ? in_a[0] : in_b[0];
        out_ternary_swapped_neq_cond = (in_cond_neq_lhs != in_cond_neq_rhs) ? in_a[0] : in_b[0];
        out_ternary_pulled_nots = in_cond ? ~in_not_then : ~in_not_else;
        out_ternary_inc = in_cond ? (in_a + CONST_ONE_8) : in_a;
        out_ternary_dec = in_cond ? (in_a - CONST_ONE_8) : in_a;
        out_ternary_1bit_0then = in_cond ? CONST_ZERO_1 : in_bit;
        out_ternary_1bit_1then = in_cond ? CONST_ONE_1 : in_bit;
        out_ternary_1bit_0else = in_cond ? in_bit : CONST_ZERO_1;
        out_ternary_1bit_1else = in_cond ? in_bit : CONST_ONE_1;
    end
endmodule

module case_parallel_simple_mod (
    input logic [3:0] case_inside_val,
    output logic [4:0] internal_out
);
    always @* begin
        (* parallel *)
        case (case_inside_val)
            4'd0, 4'd1: internal_out = 14;
            4'd2, 4'd3: internal_out = 15;
            default: internal_out = 18;
        endcase
    end
endmodule

module mod_case_unique_priority (
    input bit [2:0] in_state_case,
    output bit out_priority_case,
    output bit out_unique_case
);
always_comb begin
    out_unique_case = 1'b0;
    unique case (in_state_case)
        3'd0: out_unique_case = 1'b0;
        3'd1: out_unique_case = 1'b1;
        3'd2: out_unique_case = 1'b0;
        3'd1: out_unique_case = 1'b1;
        default: out_unique_case = 1'b1;
    endcase
end
always_comb begin
    out_priority_case = 1'b0;
    priority case (in_state_case)
        3'd0: out_priority_case = 1'b0;
        3'd1: out_priority_case = 1'b1;
        3'd2: out_priority_case = 1'b0;
        3'd1: out_priority_case = 1'b1;
        default: out_priority_case = 1'b1;
    endcase
end
endmodule

module mod_default_disable (
    input bit enable_in,
    output bit out
);
    assign out = enable_in;
endmodule

module mod_fixup_target (
    input logic fs_in_target,
    output logic fs_out_target
);
    assign fs_out_target = fs_in_target;
endmodule

module named_block_logic (
    input logic i_gate,
    input logic i_in,
    output logic o_out
);
    logic r_internal;
    logic r_temp;
    always_comb begin : my_combinational_block
        r_temp = i_in & i_gate;
        r_internal = r_temp;
        o_out = r_internal;
    end
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
    input logic [3:0] inj_case_inside_val_1755004204240_300,
    input logic inj_condition_o_1755004204133_547,
    input wire [3:0] inj_data_c_1755004204264_958,
    input bit inj_enable_in_1755004204209_354,
    input wire [7:0] inj_in_a_1755004204200_277,
    input wire [7:0] inj_in_b_1755004204200_209,
    input wire inj_in_bit_1755004204200_176,
    input wire [7:0] inj_in_c_1755004204200_422,
    input wire inj_in_cond_neq_rhs_1755004204200_452,
    input logic [7:0] inj_in_false_o_1755004204133_5,
    input wire [7:0] inj_in_latch_data_1755004204138_739,
    input bit [3:0] inj_in_mask_z_1755004204133_494,
    input wire [7:0] inj_in_not_then_1755004204200_937,
    input bit [2:0] inj_in_state_case_1755004204135_706,
    input logic [7:0] inj_in_true_o_1755004204133_679,
    input logic [1:0] inj_in_val_1755004204134_256,
    input logic [31:0] inj_input_pa_1755004204326_309,
    input logic [15:0] inj_packed_in_1755004204192_398,
    input wire [1:0] inj_selector_1755004204264_985,
    input logic [2:0] inj_shift_val_1755004204299_948,
    input int inj_val_b_1755004204152_100,
    input int inj_val_in_1755004204132_300,
    input logic [63:0] inj_wide_a_1755004204139_652,
    input logic [63:0] inj_wide_b_1755004204139_395,
    input logic [63:0] inj_wide_c_1755004204139_359,
    input wire reset,
    output logic inj_concat_port_output_1755004204136_369,
    output logic inj_cond_out_1755004204219_662,
    output logic [7:0] inj_data_out_fmt_1755004204141_821,
    output int inj_driven_var_1755004204132_387,
    output logic [7:0] inj_field0_byte_o_1755004204192_444,
    output wire inj_fs_out_1755004204276_880,
    output logic [5:0] inj_indicators_1755004204152_937,
    output logic [4:0] inj_internal_out_1755004204240_357,
    output logic [4:0] inj_internal_out_1755004204288_589,
    output logic inj_is_even_1755004204185_993,
    output logic [7:0] inj_left_shift_log_1755004204299_253,
    output logic [1:0] inj_non_ansi_i_1755004204136_34,
    output logic [1:0] inj_non_ansi_j_1755004204136_108,
    output logic [7:0] inj_o1_s_1755004204313_438,
    output logic [7:0] inj_o2_s_1755004204313_319,
    output logic [7:0] inj_o3_s_1755004204313_385,
    output logic inj_o_out_1755004204396_469,
    output logic inj_o_reg_out_1755004204144_724,
    output logic [7:0] inj_o_target_result_1755004204251_512,
    output wire inj_o_wire_out_1755004204144_119,
    output logic [7:0] inj_out1_a_1755004204172_155,
    output bit inj_out_1755004204209_382,
    output logic [15:0] inj_out_1755004204414_705,
    output logic [1:0] inj_out_bits_1755004204177_309,
    output logic [3:0] inj_out_case_case_1755004204264_320,
    output logic [3:0] inj_out_case_casex_1755004204264_514,
    output logic [3:0] inj_out_case_casez_1755004204264_519,
    output logic inj_out_comb_1755004204161_261,
    output logic inj_out_eq_1755004204200_590,
    output logic inj_out_eq_1755004204343_955,
    output logic inj_out_eq_concat_1755004204200_648,
    output logic inj_out_eq_concat_1755004204343_144,
    output logic inj_out_g_1755004204166_403,
    output logic inj_out_gt_1755004204200_86,
    output logic inj_out_gt_1755004204343_415,
    output logic inj_out_gte_1755004204200_541,
    output logic inj_out_gte_1755004204343_815,
    output reg [7:0] inj_out_latch_reg_1755004204138_256,
    output logic inj_out_lt_1755004204200_877,
    output logic inj_out_lt_1755004204343_864,
    output logic inj_out_lte_1755004204200_46,
    output logic inj_out_lte_1755004204343_587,
    output bit [1:0] inj_out_match_type_z_1755004204133_710,
    output logic inj_out_neq_1755004204200_186,
    output logic inj_out_neq_1755004204343_496,
    output logic inj_out_not_eq_1755004204200_445,
    output logic inj_out_not_eq_1755004204343_713,
    output logic inj_out_not_neq_1755004204200_521,
    output logic inj_out_not_neq_1755004204343_993,
    output bit inj_out_priority_case_1755004204135_888,
    output logic inj_out_reg_1755004204161_772,
    output logic [7:0] inj_out_reg_d_1755004204148_100,
    output reg inj_out_res_1755004204134_587,
    output reg inj_out_res_1755004204377_423,
    output logic inj_out_ternary_1755004204200_455,
    output logic inj_out_ternary_1755004204343_281,
    output logic inj_out_ternary_1bit_0else_1755004204200_21,
    output logic inj_out_ternary_1bit_0else_1755004204343_840,
    output logic inj_out_ternary_1bit_0then_1755004204200_759,
    output logic inj_out_ternary_1bit_0then_1755004204343_40,
    output logic inj_out_ternary_1bit_1else_1755004204200_291,
    output logic inj_out_ternary_1bit_1else_1755004204343_267,
    output logic inj_out_ternary_1bit_1then_1755004204200_318,
    output logic inj_out_ternary_1bit_1then_1755004204343_303,
    output logic inj_out_ternary_const_cond_false_1755004204200_747,
    output logic inj_out_ternary_const_cond_false_1755004204343_631,
    output logic inj_out_ternary_const_cond_true_1755004204200_145,
    output logic inj_out_ternary_const_cond_true_1755004204343_519,
    output logic [7:0] inj_out_ternary_dec_1755004204200_170,
    output logic [7:0] inj_out_ternary_dec_1755004204343_977,
    output logic [7:0] inj_out_ternary_inc_1755004204200_713,
    output logic [7:0] inj_out_ternary_inc_1755004204343_430,
    output logic [7:0] inj_out_ternary_pulled_nots_1755004204200_57,
    output logic [7:0] inj_out_ternary_pulled_nots_1755004204343_549,
    output logic inj_out_ternary_swapped_cond_1755004204200_612,
    output logic inj_out_ternary_swapped_cond_1755004204343_916,
    output logic inj_out_ternary_swapped_neq_cond_1755004204200_723,
    output logic inj_out_ternary_swapped_neq_cond_1755004204343_839,
    output bit inj_out_unique_case_1755004204135_739,
    output logic [7:0] inj_out_val_o_1755004204133_779,
    output logic inj_out_valid_1755004204360_155,
    output logic [7:0] inj_out_var_1755004204157_842,
    output logic [7:0] inj_out_vec_y_1755004204230_908,
    output logic [7:0] inj_output_pa_1755004204326_485,
    output logic [7:0] inj_output_pa_element1_1755004204326_696,
    output logic [7:0] inj_right_shift_arith_1755004204299_633,
    output logic [7:0] inj_right_shift_log_1755004204299_542,
    output logic [63:0] inj_wide_out_1755004204139_74
);
    // BEGIN: m_driver_check_ts1755004204132
    int my_driven_var_ts1755004204132;
        // BEGIN: non_ansi_concat_port_ts1755004204136
        output logic [1:0] inj_non_ansi_i_1755004204136_34_ts1755004204136;
        output logic [1:0] inj_non_ansi_j_1755004204136_108_ts1755004204136;
        input logic inj_condition_o_1755004204133_547_ts1755004204136;
        output logic inj_concat_port_output_1755004204136_369_ts1755004204136;
            // BEGIN: formatting_stress_ts1755004204142
            logic [7:0] temp_reg_fmt_ts1755004204141; 
            always_comb begin : stress_comb_block_label 
                inj_data_out_fmt_1755004204141_821 = 8'hXX; 
                if (inj_condition_o_1755004204133_547_ts1755004204136) begin
                    if (inj_condition_o_1755004204133_547) begin
                        case (inj_in_val_1755004204134_256) 
                            2'b00: inj_data_out_fmt_1755004204141_821 = inj_in_false_o_1755004204133_5;
                            2'b01: begin 
                                inj_data_out_fmt_1755004204141_821 = ~inj_in_false_o_1755004204133_5; 
                                end 
                            2'b10: begin 
                                logic [7:0] added_val_ts1755004204141; 
                                    // BEGIN: nets_alias_clocking_ts1755004204144
                                    wire  w_internal_ts1755004204144;
                                    logic r_internal_ts1755004204144;
                                        // BEGIN: not_a_hierarchical_scope_diag_mod_ts1755004204157
                                        logic [7:0] simple_var_nahsdm_ts1755004204157;
                                            // BEGIN: ModClockedWithSimpleAssign_ts1755004204161
                                            logic internal_reg_ts1755004204161;
                                                // BEGIN: cast_select_demo_ts1755004204178
                                                logic [7:0] internal_ts1755004204178;
                                                    // BEGIN: mod_fixup_syntax_user_ts1755004204276
                                                    logic fixup_out_val_ts1755004204276;
                                                        // BEGIN: ModuleImplicitPort_ts1755004204360
                                                        logic valid_ts1755004204360;
                                                            // BEGIN: always_comb_assign_ts1755004204414
                                                            always_comb begin
                                                                inj_out_1755004204414_705 = inj_packed_in_1755004204192_398;
                                                            end
                                                            // END: always_comb_assign_ts1755004204414

                                                            named_block_logic named_block_logic_inst_1755004204396_6000 (
                                                                .o_out(inj_o_out_1755004204396_469),
                                                                .i_gate(r_internal_ts1755004204144),
                                                                .i_in(valid_ts1755004204360)
                                                            );
                                                            // BEGIN: case_empty_statement_ts1755004204377
                                                            always_comb begin
                                                                inj_out_res_1755004204377_423 = 1'b0;
                                                                case (inj_in_val_1755004204134_256)
                                                                    2'b00: inj_out_res_1755004204377_423 = 1'b1;
                                                                    2'b01: ;
                                                                    2'b10: inj_out_res_1755004204377_423 = 1'b0;
                                                                    default: inj_out_res_1755004204377_423 = 1'b1;
                                                                endcase
                                                            end
                                                            // END: case_empty_statement_ts1755004204377

                                                        assign valid_ts1755004204360 = |simple_var_nahsdm_ts1755004204157;
                                                        assign inj_out_valid_1755004204360_155 = valid_ts1755004204360;
                                                        // END: ModuleImplicitPort_ts1755004204360

                                                        Mod_TernaryLogic Mod_TernaryLogic_inst_1755004204343_359 (
                                                            .out_eq_concat(inj_out_eq_concat_1755004204343_144),
                                                            .out_not_eq(inj_out_not_eq_1755004204343_713),
                                                            .out_ternary_dec(inj_out_ternary_dec_1755004204343_977),
                                                            .out_ternary(inj_out_ternary_1755004204343_281),
                                                            .in_a(inj_in_c_1755004204200_422),
                                                            .out_ternary_1bit_1then(inj_out_ternary_1bit_1then_1755004204343_303),
                                                            .out_ternary_1bit_0else(inj_out_ternary_1bit_0else_1755004204343_840),
                                                            .in_c(inj_in_latch_data_1755004204138_739),
                                                            .out_ternary_1bit_0then(inj_out_ternary_1bit_0then_1755004204343_40),
                                                            .out_ternary_inc(inj_out_ternary_inc_1755004204343_430),
                                                            .in_not_then(inj_in_not_then_1755004204200_937),
                                                            .out_ternary_const_cond_true(inj_out_ternary_const_cond_true_1755004204343_519),
                                                            .out_lte(inj_out_lte_1755004204343_587),
                                                            .out_ternary_swapped_cond(inj_out_ternary_swapped_cond_1755004204343_916),
                                                            .out_neq(inj_out_neq_1755004204343_496),
                                                            .in_not_else(inj_in_b_1755004204200_209),
                                                            .out_not_neq(inj_out_not_neq_1755004204343_993),
                                                            .in_b(inj_in_a_1755004204200_277),
                                                            .out_eq(inj_out_eq_1755004204343_955),
                                                            .out_lt(inj_out_lt_1755004204343_864),
                                                            .out_gte(inj_out_gte_1755004204343_815),
                                                            .in_cond_not(inj_in_bit_1755004204200_176),
                                                            .in_bit(inj_in_cond_neq_rhs_1755004204200_452),
                                                            .out_ternary_pulled_nots(inj_out_ternary_pulled_nots_1755004204343_549),
                                                            .in_cond(reset),
                                                            .in_cond_neq_lhs(w_internal_ts1755004204144),
                                                            .out_gt(inj_out_gt_1755004204343_415),
                                                            .in_cond_neq_rhs(clk),
                                                            .out_ternary_1bit_1else(inj_out_ternary_1bit_1else_1755004204343_267),
                                                            .out_ternary_const_cond_false(inj_out_ternary_const_cond_false_1755004204343_631),
                                                            .out_ternary_swapped_neq_cond(inj_out_ternary_swapped_neq_cond_1755004204343_839)
                                                        );
                                                        // BEGIN: module_packed_array_ts1755004204327
                                                        logic [7:0] my_packed_array[0:3] ;
                                                        always_comb begin
                                                            if (internal_reg_ts1755004204161) begin
                                                                my_packed_array[0] = inj_input_pa_1755004204326_309[7:0];
                                                                my_packed_array[1] = inj_input_pa_1755004204326_309[15:8];
                                                                my_packed_array[2] = inj_input_pa_1755004204326_309[23:16];
                                                                my_packed_array[3] = my_packed_array[0] + my_packed_array[1];
                                                            end else begin
                                                                my_packed_array[0] = 8'h0;
                                                                my_packed_array[1] = 8'h0;
                                                                my_packed_array[2] = 8'h0;
                                                                my_packed_array[3] = 8'h0;
                                                            end
                                                            my_packed_array[0][3:0] = inj_case_inside_val_1755004204240_300;
                                                        end
                                                        assign inj_output_pa_1755004204326_485 = my_packed_array[3];
                                                        assign inj_output_pa_element1_1755004204326_696 = my_packed_array[1];
                                                        // END: module_packed_array_ts1755004204327

                                                        split_complex_nb split_complex_nb_inst_1755004204313_6221 (
                                                            .i3_s(inj_in_true_o_1755004204133_679),
                                                            .o1_s(inj_o1_s_1755004204313_438),
                                                            .o2_s(inj_o2_s_1755004204313_319),
                                                            .o3_s(inj_o3_s_1755004204313_385),
                                                            .clk_s(clk),
                                                            .i1_s(temp_reg_fmt_ts1755004204141),
                                                            .i2_s(internal_ts1755004204178)
                                                        );
                                                        // BEGIN: ShiftOperations_ts1755004204300
                                                        assign inj_left_shift_log_1755004204299_253 = simple_var_nahsdm_ts1755004204157 << inj_shift_val_1755004204299_948;
                                                        assign inj_right_shift_log_1755004204299_542 = simple_var_nahsdm_ts1755004204157 >> inj_shift_val_1755004204299_948;
                                                        assign inj_right_shift_arith_1755004204299_633 = $signed(simple_var_nahsdm_ts1755004204157) >>> inj_shift_val_1755004204299_948;
                                                        // END: ShiftOperations_ts1755004204300

                                                        case_parallel_simple_mod case_parallel_simple_mod_inst_1755004204288_7306 (
                                                            .case_inside_val(inj_case_inside_val_1755004204240_300),
                                                            .internal_out(inj_internal_out_1755004204288_589)
                                                        );
                                                    mod_fixup_target fixup_inst (
                                                        .fs_in_target(inj_condition_o_1755004204133_547_ts1755004204136),
                                                        .fs_out_target(fixup_out_val_ts1755004204276)
                                                    );
                                                    assign inj_fs_out_1755004204276_880 = fixup_out_val_ts1755004204276;
                                                    // END: mod_fixup_syntax_user_ts1755004204276

                                                    CaseStatementConditions CaseStatementConditions_inst_1755004204264_5059 (
                                                        .data_c(inj_data_c_1755004204264_958),
                                                        .selector(inj_selector_1755004204264_985),
                                                        .out_case_case(inj_out_case_case_1755004204264_320),
                                                        .out_case_casez(inj_out_case_casez_1755004204264_519),
                                                        .out_case_casex(inj_out_case_casex_1755004204264_514)
                                                    );
                                                    // BEGIN: target_module_for_bind_ts1755004204251
                                                    always_comb inj_o_target_result_1755004204251_512 = added_val_ts1755004204141 + 1;
                                                    // END: target_module_for_bind_ts1755004204251

                                                    // BEGIN: case_unique_casez_reordered_mod_ts1755004204240
                                                    always @* begin
                                                        unique casez ({inj_non_ansi_i_1755004204136_34_ts1755004204136[0], inj_case_inside_val_1755004204240_300[3:2], inj_non_ansi_i_1755004204136_34_ts1755004204136[1]})
                                                            4'b1?0?: inj_internal_out_1755004204240_357 = 30;
                                                            4'b?101: inj_internal_out_1755004204240_357 = 31;  
                                                            4'b0?1?: inj_internal_out_1755004204240_357 = 32;
                                                            4'b1?1?: inj_internal_out_1755004204240_357 = 33;  
                                                            4'b?111: inj_internal_out_1755004204240_357 = 34;  
                                                        endcase
                                                    end
                                                    // END: case_unique_casez_reordered_mod_ts1755004204240

                                                    split_vector_assign split_vector_assign_inst_1755004204230_2411 (
                                                        .clk_y(clk),
                                                        .condition_y(internal_reg_ts1755004204161),
                                                        .in_val_y(inj_in_true_o_1755004204133_679),
                                                        .out_vec_y(inj_out_vec_y_1755004204230_908)
                                                    );
                                                    // BEGIN: mod_logical_not_ts1755004204219
                                                    always_comb begin
                                                        inj_cond_out_1755004204219_662 = !internal_reg_ts1755004204161;
                                                    end
                                                    // END: mod_logical_not_ts1755004204219

                                                    mod_default_disable mod_default_disable_inst_1755004204209_8961 (
                                                        .enable_in(inj_enable_in_1755004204209_354),
                                                        .out(inj_out_1755004204209_382)
                                                    );
                                                    Mod_TernaryLogic Mod_TernaryLogic_inst_1755004204200_1931 (
                                                        .out_lt(inj_out_lt_1755004204200_877),
                                                        .out_eq_concat(inj_out_eq_concat_1755004204200_648),
                                                        .in_cond_not(w_internal_ts1755004204144),
                                                        .in_not_then(inj_in_not_then_1755004204200_937),
                                                        .in_not_else(inj_in_latch_data_1755004204138_739),
                                                        .in_b(inj_in_b_1755004204200_209),
                                                        .out_ternary_1bit_0else(inj_out_ternary_1bit_0else_1755004204200_21),
                                                        .out_ternary_dec(inj_out_ternary_dec_1755004204200_170),
                                                        .out_lte(inj_out_lte_1755004204200_46),
                                                        .out_not_eq(inj_out_not_eq_1755004204200_445),
                                                        .out_gt(inj_out_gt_1755004204200_86),
                                                        .in_a(inj_in_a_1755004204200_277),
                                                        .out_ternary_swapped_neq_cond(inj_out_ternary_swapped_neq_cond_1755004204200_723),
                                                        .in_c(inj_in_c_1755004204200_422),
                                                        .out_neq(inj_out_neq_1755004204200_186),
                                                        .out_ternary_const_cond_false(inj_out_ternary_const_cond_false_1755004204200_747),
                                                        .out_ternary_1bit_0then(inj_out_ternary_1bit_0then_1755004204200_759),
                                                        .out_gte(inj_out_gte_1755004204200_541),
                                                        .out_ternary_const_cond_true(inj_out_ternary_const_cond_true_1755004204200_145),
                                                        .out_eq(inj_out_eq_1755004204200_590),
                                                        .out_ternary_swapped_cond(inj_out_ternary_swapped_cond_1755004204200_612),
                                                        .out_ternary(inj_out_ternary_1755004204200_455),
                                                        .out_not_neq(inj_out_not_neq_1755004204200_521),
                                                        .out_ternary_inc(inj_out_ternary_inc_1755004204200_713),
                                                        .in_bit(inj_in_bit_1755004204200_176),
                                                        .out_ternary_pulled_nots(inj_out_ternary_pulled_nots_1755004204200_57),
                                                        .out_ternary_1bit_1then(inj_out_ternary_1bit_1then_1755004204200_318),
                                                        .in_cond(reset),
                                                        .in_cond_neq_lhs(clk),
                                                        .in_cond_neq_rhs(inj_in_cond_neq_rhs_1755004204200_452),
                                                        .out_ternary_1bit_1else(inj_out_ternary_1bit_1else_1755004204200_291)
                                                    );
                                                    // BEGIN: typedef_union_mod_ts1755004204193
                                                    typedef union packed {
                                                        logic [15:0] word_ts1755004204192;
                                                        logic [1:0][7:0] byte_fields_ts1755004204192;
                                                    } my_packed_union_t;
                                                    my_packed_union_t my_union_var;
                                                    always_comb begin
                                                        my_union_var.word_ts1755004204192 = inj_packed_in_1755004204192_398;
                                                    end
                                                    assign inj_field0_byte_o_1755004204192_444 = my_union_var.byte_fields_ts1755004204192[0];
                                                    // END: typedef_union_mod_ts1755004204193

                                                    // BEGIN: FunctionTaskMod_ts1755004204185
                                                    function automatic bit check_even(input logic [7:0] v);
                                                        check_even = ~v[0];
                                                    endfunction
                                                    task automatic dummy_task(input logic [7:0] v);
                                                        int tmp_ts1755004204185;
                                                        tmp_ts1755004204185 = v;
                                                    endtask
                                                    assign inj_is_even_1755004204185_993 = check_even(simple_var_nahsdm_ts1755004204157);
                                                    // END: FunctionTaskMod_ts1755004204185

                                                always_comb begin
                                                    internal_ts1755004204178 = temp_reg_fmt_ts1755004204141;
                                                    inj_out_bits_1755004204177_309 = internal_ts1755004204178[3 -: 2];
                                                end
                                                // END: cast_select_demo_ts1755004204178

                                                // BEGIN: split_basic_blocking_ts1755004204172
                                                always @(*) begin
                                                    inj_out1_a_1755004204172_155 = inj_in_false_o_1755004204133_5;
                                                end
                                                // END: split_basic_blocking_ts1755004204172

                                                LintSeqNonBlockAssign LintSeqNonBlockAssign_inst_1755004204166_7528 (
                                                    .clk(clk),
                                                    .in_f(internal_reg_ts1755004204161),
                                                    .out_g(inj_out_g_1755004204166_403)
                                                );
                                            always @(posedge clk) begin 
                                            internal_reg_ts1755004204161 <= inj_condition_o_1755004204133_547_ts1755004204136; 
                                            end
                                            assign inj_out_comb_1755004204161_261 = inj_condition_o_1755004204133_547_ts1755004204136 ^ r_internal_ts1755004204144; 
                                            always @(posedge clk) begin 
                                            inj_out_reg_1755004204161_772 <= internal_reg_ts1755004204161 & r_internal_ts1755004204144; 
                                            end
                                            // END: ModClockedWithSimpleAssign_ts1755004204161

                                        always_comb simple_var_nahsdm_ts1755004204157 = added_val_ts1755004204141;
                                        assign inj_out_var_1755004204157_842 = simple_var_nahsdm_ts1755004204157;
                                        // END: not_a_hierarchical_scope_diag_mod_ts1755004204157

                                        // BEGIN: dup_compare_ts1755004204152
                                        always_comb begin
                                            inj_indicators_1755004204152_937 = '0;
                                            inj_indicators_1755004204152_937[0] = (my_driven_var_ts1755004204132 == inj_val_b_1755004204152_100);
                                            inj_indicators_1755004204152_937[1] = (my_driven_var_ts1755004204132 != inj_val_b_1755004204152_100);
                                            inj_indicators_1755004204152_937[2] = (my_driven_var_ts1755004204132 > inj_val_b_1755004204152_100);
                                            inj_indicators_1755004204152_937[3] = (my_driven_var_ts1755004204132 < inj_val_b_1755004204152_100);
                                            inj_indicators_1755004204152_937[4] = (my_driven_var_ts1755004204132 >= inj_val_b_1755004204152_100);
                                            inj_indicators_1755004204152_937[5] = (my_driven_var_ts1755004204132 <= inj_val_b_1755004204152_100);
                                            if (inj_val_b_1755004204152_100 == inj_val_in_1755004204132_300) begin
                                                inj_indicators_1755004204152_937 = inj_indicators_1755004204152_937 | 6'b111111;
                                            end
                                            if (my_driven_var_ts1755004204132 > inj_val_in_1755004204132_300) begin
                                                inj_indicators_1755004204152_937 = inj_indicators_1755004204152_937 & 6'b000000;
                                            end
                                            if ((my_driven_var_ts1755004204132 < inj_val_b_1755004204152_100) && (inj_val_b_1755004204152_100 > inj_val_in_1755004204132_300)) begin
                                                inj_indicators_1755004204152_937[0] = 1;
                                            end else if ((my_driven_var_ts1755004204132 >= inj_val_b_1755004204152_100) || (inj_val_b_1755004204152_100 <= inj_val_in_1755004204132_300)) begin
                                                inj_indicators_1755004204152_937[1] = 1;
                                            end
                                        end
                                        // END: dup_compare_ts1755004204152

                                        // BEGIN: split_conditional_nb_ts1755004204148
                                        always @(posedge clk) begin
                                            if (inj_condition_o_1755004204133_547) begin
                                                inj_out_reg_d_1755004204148_100 <= added_val_ts1755004204141;
                                            end else begin
                                                inj_out_reg_d_1755004204148_100 <= temp_reg_fmt_ts1755004204141;
                                            end
                                        end
                                        // END: split_conditional_nb_ts1755004204148

                                    assign w_internal_ts1755004204144  = clk & inj_concat_port_output_1755004204136_369_ts1755004204136;
                                    assign inj_o_wire_out_1755004204144_119  = w_internal_ts1755004204144;
                                    always_ff @(posedge clk) r_internal_ts1755004204144 <= inj_condition_o_1755004204133_547;
                                    assign inj_o_reg_out_1755004204144_724 = r_internal_ts1755004204144;
                                    // END: nets_alias_clocking_ts1755004204144

                                added_val_ts1755004204141 = inj_in_false_o_1755004204133_5 + 8'h01; 
                                inj_data_out_fmt_1755004204141_821 = added_val_ts1755004204141; 
                                end 
                            default: inj_data_out_fmt_1755004204141_821 = 8'hFF; 
                        endcase 
                    end else begin
                        inj_data_out_fmt_1755004204141_821 = inj_in_false_o_1755004204133_5 - 8'h01; 
                    end 
                end else begin
                    inj_data_out_fmt_1755004204141_821 = 8'h00; 
                end 
            end
            // END: formatting_stress_ts1755004204142

            // BEGIN: wide_ops_deep_ts1755004204139
            assign inj_wide_out_1755004204139_74 = (((inj_wide_a_1755004204139_652 + inj_wide_b_1755004204139_395) ^ inj_wide_c_1755004204139_359) & (~inj_wide_a_1755004204139_652 | inj_wide_b_1755004204139_395)) + (inj_wide_c_1755004204139_359 >>> 5);
            // END: wide_ops_deep_ts1755004204139

            // BEGIN: module_latch_ts1755004204138
            always_latch begin
            if (clk) begin
                inj_out_latch_reg_1755004204138_256 = inj_in_latch_data_1755004204138_739;
            end
            end
            // END: module_latch_ts1755004204138

        assign inj_non_ansi_i_1755004204136_34_ts1755004204136 = 2'b10;
        assign inj_non_ansi_j_1755004204136_108_ts1755004204136 = 2'b01;
        assign inj_concat_port_output_1755004204136_369_ts1755004204136 = inj_condition_o_1755004204133_547_ts1755004204136;
        // END: non_ansi_concat_port_ts1755004204136

        mod_case_unique_priority mod_case_unique_priority_inst_1755004204135_3907 (
            .in_state_case(inj_in_state_case_1755004204135_706),
            .out_priority_case(inj_out_priority_case_1755004204135_888),
            .out_unique_case(inj_out_unique_case_1755004204135_739)
        );
        // BEGIN: case_default_ts1755004204134
        always_comb begin
            inj_out_res_1755004204134_587 = 1'b0;
            case (inj_in_val_1755004204134_256)
                2'b01: inj_out_res_1755004204134_587 = 1'b1;
                2'b10: inj_out_res_1755004204134_587 = 1'b0;
                default: inj_out_res_1755004204134_587 = 1'b1;
            endcase
        end
        // END: case_default_ts1755004204134

        // BEGIN: mod_casez_wildcard_ts1755004204133
    always_comb begin
        casez (inj_in_mask_z_1755004204133_494)
            4'b10?0: begin
                inj_out_match_type_z_1755004204133_710 = 2'b00;
            end
            4'b011?: begin
                inj_out_match_type_z_1755004204133_710 = 2'b01;
            end
            default: begin
                inj_out_match_type_z_1755004204133_710 = 2'b11;
            end
        endcase
    end
        // END: mod_casez_wildcard_ts1755004204133

        // BEGIN: split_conditional_blocking_ts1755004204133
        always @(*) begin
            if (inj_condition_o_1755004204133_547) begin
                inj_out_val_o_1755004204133_779 = inj_in_true_o_1755004204133_679;
            end else begin
                inj_out_val_o_1755004204133_779 = inj_in_false_o_1755004204133_5;
            end
        end
        // END: split_conditional_blocking_ts1755004204133

    function automatic void write_to_var(input int val);
        my_driven_var_ts1755004204132 = val;
    endfunction
    always @(posedge clk) begin
        write_to_var(inj_val_in_1755004204132_300);
    end
    assign inj_driven_var_1755004204132_387 = my_driven_var_ts1755004204132;
    // END: m_driver_check_ts1755004204132
endmodule

