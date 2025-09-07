interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
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

module LintCombBlockAssign (
    input logic in_c,
    input logic in_d,
    output logic out_e
);
    always_comb begin
        out_e = in_c & in_d;
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

module case_unique0_violating_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        unique0 casez (case_expr)
            2'b1?: internal_out = 8;
            2'b11: internal_out = 9;  
            2'b?1: internal_out = 10; 
            2'b00: internal_out = 11; 
        endcase
    end
endmodule

module child_module_v2_config_dummy (
    input logic i,
    output logic o
);
    assign o = i | i; 
endmodule

module dup_compare (
    input int val_a,
    input int val_b,
    input int val_c,
    output logic [5:0] indicators
);
    always_comb begin
        indicators = '0;
        indicators[0] = (val_a == val_b);
        indicators[1] = (val_a != val_b);
        indicators[2] = (val_a > val_b);
        indicators[3] = (val_a < val_b);
        indicators[4] = (val_a >= val_b);
        indicators[5] = (val_a <= val_b);
        if (val_b == val_c) begin
            indicators = indicators | 6'b111111;
        end
        if (val_a > val_c) begin
            indicators = indicators & 6'b000000;
        end
        if ((val_a < val_b) && (val_b > val_c)) begin
            indicators[0] = 1;
        end else if ((val_a >= val_b) || (val_b <= val_c)) begin
            indicators[1] = 1;
        end
    end
endmodule

module dup_logic_ops (
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic [7:0] d3,
    input logic [3:0] flags,
    output logic [7:0] out1
);
    logic cond1, cond2, cond3;
    logic complex_cond1, complex_cond2;
    assign cond1 = flags[0] && flags[1];
    assign cond2 = flags[2] || flags[3];
    assign cond3 = !flags[0];
    assign complex_cond1 = (cond1 || cond2) && cond3;
    assign complex_cond2 = !(flags[0] && flags[1]) || (flags[2] || !flags[3]);
    always_comb begin
        out1 = '0;
        if (complex_cond1) begin
            out1 = d1 + d2;
        end else begin
            out1 = d1 ^ d3;
        end
        if (complex_cond2) begin
            out1 = out1 + d3;
        end else begin
            out1 = out1 - d3;
        end
        if ((flags[0] && flags[1]) && (!flags[2] || flags[3])) begin
            out1 = out1 * 2;
        end
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

module module_packed_variables (
    input logic [15:0] data_in_pa,
    input logic [7:0] data_in_pv,
    input logic enable_pv,
    output logic [7:0] data_out_pa,
    output logic [3:0] data_out_pv
);
    logic [31:0] data_pv ;
    logic [7:0] data_pa[0:1] ;
    always_comb begin
        if (enable_pv) begin
            data_pv[7:0] = data_in_pv;
            data_pv[15:8] = ~data_in_pv;
            data_pv[23:16] = data_pv[7:0];
            data_pv[31:24] = data_pv[15:8];
            data_pa[0] = data_in_pa[7:0];
            data_pa[1] = data_in_pa[15:8];
        end else begin
            data_pv = 32'h0;
            data_pa[0] = 8'h0;
            data_pa[1] = 8'h0;
        end
    end
    assign data_out_pv = data_pv[3:0];
    assign data_out_pa = data_pa[0];
endmodule

module more_ops (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    output logic anded,
    output logic diff,
    output logic ored,
    output logic [7:0] sum,
    output logic xored
);
    assign sum = a + b;
    assign diff = a > c;
    assign anded = a & b;
    assign ored = a | c;
    assign xored = a ^ b;
endmodule

module range_select_indexed_packed (
    input logic [31:0] in_vec,
    input int start_index,
    input int width,
    output logic [7:0] out_down,
    output logic [7:0] out_up
);
    always_comb begin
        if (start_index >= 0 && width > 0 && start_index + width <= 32) begin
            case (width)
                1: out_up = in_vec[start_index +: 1];
                2: out_up = in_vec[start_index +: 2];
                4: out_up = in_vec[start_index +: 4];
                8: out_up = in_vec[start_index +: 8];
                default: out_up = 'x;
            endcase
        end else begin
            out_up = 'x;
        end
        if (start_index >= width - 1 && width > 0 && start_index < 32) begin
            case (width)
                1: out_down = in_vec[start_index -: 1];
                2: out_down = in_vec[start_index -: 2];
                4: out_down = in_vec[start_index -: 4];
                8: out_down = in_vec[start_index -: 8];
                default: out_down = 'x;
            endcase
        end else begin
            out_down = 'x;
        end
    end
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module attributes_on_expr_port (
    input logic i_control,
    input logic i_in,
    output logic o_out
);
    logic internal_sig;
    assign internal_sig = i_in & i_control;
    simple_adder sa_inst(
        .a  (i_in),
        (* fanout_limit = 10 *) .b(i_control),
        .sum(o_out)
    );
endmodule

module simple_assign (
    input logic [7:0] in,
    output logic [7:0] out
);
    assign out = in;
endmodule

module simple_undeclared_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module split_if_empty_then (
    input logic clk_p,
    input logic condition_p,
    input logic [7:0] in_val_p,
    output logic [7:0] out_reg_p
);
    always @(posedge clk_p) begin
        if (condition_p) begin
        end else begin
            out_reg_p <= in_val_p;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_add_val_m1_1755007870999_860,
    input logic [1:0] inj_case_expr_1755007871035_636,
    input logic [15:0] inj_data1_1755007871084_996,
    input logic [15:0] inj_data_in_pa_1755007871006_600,
    input wire [3:0] inj_in0_1755007871001_64,
    input logic [2:0] inj_in1_1755007870997_890,
    input wire [3:0] inj_in1_1755007871001_117,
    input logic inj_in2_1755007870997_556,
    input wire [3:0] inj_in2_1755007871001_4,
    input wire [3:0] inj_in3_1755007871001_785,
    input wire [7:0] inj_in_a_1755007871044_510,
    input wire [7:0] inj_in_b_1755007871044_514,
    input wire [7:0] inj_in_c_1755007871044_953,
    input bit [7:0] inj_in_cmd_1755007871079_196,
    input wire inj_in_cond_1755007871104_246,
    input wire inj_in_cond_neq_rhs_1755007871104_914,
    input wire [7:0] inj_in_const1_1755007871044_785,
    input wire [7:0] inj_in_const2_1755007871044_65,
    input bit [3:0] inj_in_mask_z_1755007871041_918,
    input logic [7:0] inj_in_val_m1_1755007870999_560,
    input logic [31:0] inj_in_vec_1755007871018_632,
    input logic [3:0] inj_in_vector_1755007870997_492,
    input wire [1:0] inj_sel_1755007871001_599,
    input int inj_val_a_1755007870999_375,
    input int inj_val_b_1755007870999_772,
    input logic [3:0] inj_val_b_1755007871004_723,
    input int inj_val_c_1755007870999_372,
    input logic [9:0] inj_val_in_1755007871008_78,
    input wire [63:0] inj_wide_a_1755007871191_168,
    input wire [63:0] inj_wide_b_1755007871191_694,
    input wire reset,
    output logic inj_anded_1755007871014_897,
    output wire [127:0] inj_concat_out_1755007871191_81,
    output int inj_config_data_out_1755007871016_220,
    output reg [3:0] inj_data_out_1755007871003_167,
    output logic [3:0] inj_data_out_1755007871023_101,
    output int inj_data_out_1755007871026_735,
    output logic [3:0] inj_data_out_1755007871039_65,
    output logic [15:0] inj_data_out_1755007871084_213,
    output logic [15:0] inj_data_out_1755007871180_918,
    output logic [7:0] inj_data_out_pa_1755007871006_215,
    output logic [3:0] inj_data_out_pv_1755007871006_698,
    output logic inj_diff_1755007871014_561,
    output logic inj_extra_out_1755007870997_455,
    output logic inj_fs_out_target_1755007871203_265,
    output logic [5:0] inj_indicators_1755007870999_327,
    output logic [4:0] inj_internal_out_1755007871035_54,
    output logic [4:0] inj_internal_out_1755007871089_696,
    output reg [3:0] inj_mux_out_1755007871001_438,
    output logic inj_o_1755007871136_584,
    output wire inj_o_1755007871157_629,
    output logic inj_o_out_1755007871032_725,
    output logic inj_o_reg_out_1755007871053_138,
    output int inj_o_val_1755007871011_378,
    output wire inj_o_wire_out_1755007871053_375,
    output logic inj_ored_1755007871014_402,
    output logic inj_out1_1755007870997_113,
    output logic [7:0] inj_out1_1755007871049_430,
    output logic inj_out2_1755007870997_239,
    output logic [7:0] inj_out_1755007871009_727,
    output logic [7:0] inj_out_1755007871072_252,
    output logic [7:0] inj_out_1755007871168_476,
    output logic [7:0] inj_out_add_assoc_1755007871044_492,
    output logic [7:0] inj_out_and_assoc_1755007871044_763,
    output logic [7:0] inj_out_and_swap_const_1755007871044_310,
    output logic [7:0] inj_out_arith_1755007871044_351,
    output logic [1:0] inj_out_bits_1755007871029_205,
    output logic [1:0] inj_out_bits_1755007871114_502,
    output logic [7:0] inj_out_bitwise_1755007871044_512,
    output logic [7:0] inj_out_data_1755007871126_198,
    output logic [7:0] inj_out_down_1755007871018_688,
    output logic inj_out_e_1755007871215_645,
    output logic inj_out_eq_1755007871104_355,
    output logic inj_out_eq_concat_1755007871104_400,
    output logic inj_out_gt_1755007871104_498,
    output logic inj_out_gte_1755007871104_571,
    output logic inj_out_logical_1755007871044_281,
    output logic inj_out_lt_1755007871104_41,
    output logic inj_out_lte_1755007871104_134,
    output bit [1:0] inj_out_match_type_z_1755007871041_40,
    output logic [7:0] inj_out_mul_assoc_1755007871044_457,
    output logic [7:0] inj_out_negate_1755007871044_562,
    output logic inj_out_neq_1755007871104_206,
    output logic inj_out_not_eq_1755007871104_892,
    output logic inj_out_not_neq_1755007871104_740,
    output logic [7:0] inj_out_or_assoc_1755007871044_226,
    output logic [7:0] inj_out_or_swap_not_1755007871044_77,
    output logic [7:0] inj_out_reg_p_1755007871020_406,
    output reg inj_out_res_1755007871227_930,
    output logic inj_out_single_1755007870997_841,
    output logic [7:0] inj_out_slice_1755007871096_673,
    output bit [3:0] inj_out_status_1755007871079_474,
    output logic [7:0] inj_out_sum_m1_1755007870999_891,
    output logic inj_out_ternary_1755007871104_706,
    output logic inj_out_ternary_1bit_0else_1755007871104_944,
    output logic inj_out_ternary_1bit_0then_1755007871104_931,
    output logic inj_out_ternary_1bit_1else_1755007871104_15,
    output logic inj_out_ternary_1bit_1then_1755007871104_346,
    output logic inj_out_ternary_const_cond_false_1755007871104_554,
    output logic inj_out_ternary_const_cond_true_1755007871104_404,
    output logic [7:0] inj_out_ternary_dec_1755007871104_547,
    output logic [7:0] inj_out_ternary_inc_1755007871104_99,
    output logic [7:0] inj_out_ternary_pulled_nots_1755007871104_608,
    output logic inj_out_ternary_swapped_cond_1755007871104_915,
    output logic inj_out_ternary_swapped_neq_cond_1755007871104_3,
    output logic [7:0] inj_out_unary_not_1755007871044_29,
    output logic [7:0] inj_out_up_1755007871018_139,
    output int inj_out_val_1755007871042_788,
    output int inj_out_val_1755007871146_775,
    output logic inj_out_wire_1755007871059_599,
    output logic [7:0] inj_out_xor_assoc_1755007871044_99,
    output logic [7:0] inj_out_xor_swap_var_1755007871044_563,
    output logic inj_protected_active_1755007870998_602,
    output wire [7:0] inj_reduce_xor_out_1755007871191_100,
    output logic [3:0] inj_result_1755007871004_570,
    output logic [7:0] inj_sum_1755007871014_280,
    output logic [9:0] inj_val_out_1755007871008_11,
    output logic [7:0] inj_var_out_m1_1755007870999_197,
    output wire [63:0] inj_wide_sum_1755007871191_792,
    output logic inj_write_status_1755007871065_492,
    output logic inj_xored_1755007871014_100
);
    // BEGIN: combinatorial_logic_ts1755007870997
    // BEGIN: ansi_implicit_inherit_ts1755007870997
    // BEGIN: PragmaProtectBoundaries_ts1755007870998
logic internal_state_ts1755007870998;
    // BEGIN: expr_preadd_comb_ts1755007871000
    logic [7:0] var_m1_ts1755007871000;
        // BEGIN: mod_automatic_task_ts1755007871012
        task automatic update_val(input int in_v, output int out_v);
            out_v = in_v * 2;
        endtask
        always_comb begin
            int temp_val_ts1755007871012;
                // BEGIN: cast_select_demo_ts1755007871029
                logic [7:0] internal_ts1755007871029;
                    // BEGIN: Mod_BasicOps_ts1755007871046
                    logic [7:0] intermediate_arith_ts1755007871046;
                    logic [7:0] intermediate_bitwise_ts1755007871046;
                    logic [0:0] intermediate_logical_ts1755007871046;
                    logic [7:0] intermediate_add_assoc_ts1755007871046;
                    logic [7:0] intermediate_mul_assoc_ts1755007871046;
                    logic [7:0] intermediate_and_assoc_ts1755007871046;
                    logic [7:0] intermediate_or_assoc_ts1755007871046;
                    logic [7:0] intermediate_xor_assoc_ts1755007871046;
                        // BEGIN: nets_alias_clocking_ts1755007871053
                        wire  w_internal_ts1755007871053;
                        logic r_internal_ts1755007871053;
                            // BEGIN: cast_select_demo_ts1755007871114
                            logic [7:0] internal_ts1755007871114;
                                // BEGIN: casez_xz_alt_ts1755007871228
                                always_comb begin
                                    inj_out_res_1755007871227_930 = 1'b0;
                                    casez (inj_in1_1755007870997_890)
                                        3'b1?z: inj_out_res_1755007871227_930 = 1'b1;
                                        3'b0z?: inj_out_res_1755007871227_930 = 1'b0;
                                        default: inj_out_res_1755007871227_930 = 1'b1;
                                    endcase
                                end
                                // END: casez_xz_alt_ts1755007871228

                                LintCombBlockAssign LintCombBlockAssign_inst_1755007871215_1635 (
                                    .out_e(inj_out_e_1755007871215_645),
                                    .in_c(r_internal_ts1755007871053),
                                    .in_d(inj_in2_1755007870997_556)
                                );
                                // BEGIN: mod_fixup_target_ts1755007871203
                                assign inj_fs_out_target_1755007871203_265 = r_internal_ts1755007871053;
                                // END: mod_fixup_target_ts1755007871203

                                // BEGIN: wide_bus_ops_ts1755007871191
                                assign inj_wide_sum_1755007871191_792 = inj_wide_a_1755007871191_168 + inj_wide_b_1755007871191_694;
                                assign inj_reduce_xor_out_1755007871191_100 = ^inj_wide_a_1755007871191_168[63:0];
                                assign inj_concat_out_1755007871191_81 = {inj_wide_a_1755007871191_168, inj_wide_b_1755007871191_694};
                                // END: wide_bus_ops_ts1755007871191

                                // BEGIN: SequentialLogicPlaceholder_ts1755007871180
                                always_ff @(posedge clk or posedge reset) begin
                                    if (reset) begin
                                        inj_data_out_1755007871180_918 <= 16'h0;
                                    end else begin
                                        inj_data_out_1755007871180_918 <= inj_data1_1755007871084_996;
                                    end
                                end
                                // END: SequentialLogicPlaceholder_ts1755007871180

                                // BEGIN: simple_assign_ts1755007871168
                                assign inj_out_1755007871168_476 = intermediate_or_assoc_ts1755007871046;
                                // END: simple_assign_ts1755007871168

                                // BEGIN: buf_primitive_ts1755007871157
                                buf b1 (inj_o_1755007871157_629, inj_in_cond_1755007871104_246);
                                // END: buf_primitive_ts1755007871157

                                // BEGIN: module_in_program_ref_ts1755007871146
                                assign inj_out_val_1755007871146_775 = inj_val_a_1755007870999_375;
                                // END: module_in_program_ref_ts1755007871146

                                child_module_v2_config_dummy child_module_v2_config_dummy_inst_1755007871136_2349 (
                                    .o(inj_o_1755007871136_584),
                                    .i(r_internal_ts1755007871053)
                                );
                                // BEGIN: SimpleAssign_ts1755007871126
                                assign inj_out_data_1755007871126_198 = intermediate_mul_assoc_ts1755007871046;
                                // END: SimpleAssign_ts1755007871126

                            always_comb begin
                                internal_ts1755007871114 = intermediate_add_assoc_ts1755007871046;
                                inj_out_bits_1755007871114_502 = internal_ts1755007871114[3 -: 2];
                            end
                            // END: cast_select_demo_ts1755007871114

                            Mod_TernaryLogic Mod_TernaryLogic_inst_1755007871104_8635 (
                                .out_ternary_const_cond_true(inj_out_ternary_const_cond_true_1755007871104_404),
                                .in_cond(inj_in_cond_1755007871104_246),
                                .in_not_then(inj_in_b_1755007871044_514),
                                .in_b(inj_in_c_1755007871044_953),
                                .in_cond_not(w_internal_ts1755007871053),
                                .out_neq(inj_out_neq_1755007871104_206),
                                .out_gte(inj_out_gte_1755007871104_571),
                                .out_lte(inj_out_lte_1755007871104_134),
                                .in_cond_neq_rhs(inj_in_cond_neq_rhs_1755007871104_914),
                                .in_c(inj_in_a_1755007871044_510),
                                .out_not_eq(inj_out_not_eq_1755007871104_892),
                                .out_ternary_inc(inj_out_ternary_inc_1755007871104_99),
                                .out_ternary_dec(inj_out_ternary_dec_1755007871104_547),
                                .out_ternary_const_cond_false(inj_out_ternary_const_cond_false_1755007871104_554),
                                .in_a(inj_in_const1_1755007871044_785),
                                .in_cond_neq_lhs(reset),
                                .out_ternary_1bit_1then(inj_out_ternary_1bit_1then_1755007871104_346),
                                .out_eq_concat(inj_out_eq_concat_1755007871104_400),
                                .out_ternary(inj_out_ternary_1755007871104_706),
                                .in_not_else(inj_in_const2_1755007871044_65),
                                .out_ternary_1bit_0else(inj_out_ternary_1bit_0else_1755007871104_944),
                                .out_ternary_1bit_0then(inj_out_ternary_1bit_0then_1755007871104_931),
                                .out_eq(inj_out_eq_1755007871104_355),
                                .in_bit(clk),
                                .out_ternary_1bit_1else(inj_out_ternary_1bit_1else_1755007871104_15),
                                .out_lt(inj_out_lt_1755007871104_41),
                                .out_not_neq(inj_out_not_neq_1755007871104_740),
                                .out_ternary_swapped_cond(inj_out_ternary_swapped_cond_1755007871104_915),
                                .out_ternary_pulled_nots(inj_out_ternary_pulled_nots_1755007871104_608),
                                .out_gt(inj_out_gt_1755007871104_498),
                                .out_ternary_swapped_neq_cond(inj_out_ternary_swapped_neq_cond_1755007871104_3)
                            );
                            // BEGIN: MiscExpressions_ValueRange_ts1755007871096
                            always_comb begin
                                inj_out_slice_1755007871096_673 = inj_data_in_pa_1755007871006_600[7:0];
                            end
                            // END: MiscExpressions_ValueRange_ts1755007871096

                            // BEGIN: case_full_simple_mod_ts1755007871090
                            always @* begin
                                (* full *)
                                case (inj_case_expr_1755007871035_636)
                                    2'b00: inj_internal_out_1755007871089_696 = 10;
                                    2'b01: inj_internal_out_1755007871089_696 = 11;
                                    2'b10: inj_internal_out_1755007871089_696 = 12;
                                    default: inj_internal_out_1755007871089_696 = 13;
                                endcase
                            end
                            // END: case_full_simple_mod_ts1755007871090

                            CombinationalLogicExplicit CombinationalLogicExplicit_inst_1755007871084_5748 (
                                .data_out(inj_data_out_1755007871084_213),
                                .data0(inj_data_in_pa_1755007871006_600),
                                .data1(inj_data1_1755007871084_996),
                                .sel(inj_in2_1755007870997_556)
                            );
                            // BEGIN: mod_case_standard_ts1755007871080
                        always_comb begin
                            case (inj_in_cmd_1755007871079_196)
                                8'd0, 8'd1, 8'd2: begin
                                    inj_out_status_1755007871079_474 = 4'hA;
                                end
                                8'd3, 8'd4: begin
                                    inj_out_status_1755007871079_474 = 4'hB;
                                end
                                default: begin
                                    inj_out_status_1755007871079_474 = 4'hF;
                                end
                            endcase
                        end
                            // END: mod_case_standard_ts1755007871080

                            // BEGIN: timed_assign_unhandled_ts1755007871072
                            always @(posedge clk) begin
                                inj_out_1755007871072_252 <= intermediate_mul_assoc_ts1755007871046;
                            end
                            // END: timed_assign_unhandled_ts1755007871072

                            // BEGIN: module_sequential_writes_ts1755007871065
                            my_if vif_bus();
                            always_comb begin
                                vif_bus.data = intermediate_add_assoc_ts1755007871046;
                                vif_bus.ready = 1'b1;
                                vif_bus.valid = 1'b0;
                                inj_write_status_1755007871065_492 = vif_bus.ready;
                            end
                            // END: module_sequential_writes_ts1755007871065

                            // BEGIN: net_var_conn_child_ts1755007871059
                            assign inj_out_wire_1755007871059_599 = inj_in2_1755007870997_556;
                            // END: net_var_conn_child_ts1755007871059

                        assign w_internal_ts1755007871053  = reset & inj_in2_1755007870997_556;
                        assign inj_o_wire_out_1755007871053_375  = w_internal_ts1755007871053;
                        always_ff @(posedge clk) r_internal_ts1755007871053 <= internal_state_ts1755007870998;
                        assign inj_o_reg_out_1755007871053_138 = r_internal_ts1755007871053;
                        // END: nets_alias_clocking_ts1755007871053

                        dup_logic_ops dup_logic_ops_inst_1755007871049_6931 (
                            .d1(intermediate_xor_assoc_ts1755007871046),
                            .d2(intermediate_arith_ts1755007871046),
                            .d3(intermediate_add_assoc_ts1755007871046),
                            .flags(inj_val_b_1755007871004_723),
                            .out1(inj_out1_1755007871049_430)
                        );
                    parameter [7:0] CONST_ZERO = 8'h00;
                    always_comb begin
                        intermediate_arith_ts1755007871046 = inj_in_a_1755007871044_510;
                        intermediate_arith_ts1755007871046 = intermediate_arith_ts1755007871046 + inj_in_b_1755007871044_514;
                        intermediate_arith_ts1755007871046 = intermediate_arith_ts1755007871046 - inj_in_c_1755007871044_953;
                        intermediate_arith_ts1755007871046 = intermediate_arith_ts1755007871046 * inj_in_const1_1755007871044_785;
                        if (inj_in_b_1755007871044_514 != CONST_ZERO) begin
                            intermediate_arith_ts1755007871046 = intermediate_arith_ts1755007871046 / inj_in_b_1755007871044_514;
                            intermediate_arith_ts1755007871046 = intermediate_arith_ts1755007871046 % inj_in_b_1755007871044_514;
                        end else begin
                            intermediate_arith_ts1755007871046 = 'x;
                        end
                        inj_out_arith_1755007871044_351 = intermediate_arith_ts1755007871046;
                        intermediate_bitwise_ts1755007871046 = inj_in_a_1755007871044_510;
                        intermediate_bitwise_ts1755007871046 = intermediate_bitwise_ts1755007871046 & inj_in_b_1755007871044_514;
                        intermediate_bitwise_ts1755007871046 = intermediate_bitwise_ts1755007871046 | inj_in_c_1755007871044_953;
                        intermediate_bitwise_ts1755007871046 = intermediate_bitwise_ts1755007871046 ^ inj_in_const1_1755007871044_785;
                        inj_out_bitwise_1755007871044_512 = intermediate_bitwise_ts1755007871046;
                        intermediate_logical_ts1755007871046 = (inj_in_a_1755007871044_510 != CONST_ZERO) && (inj_in_b_1755007871044_514 != CONST_ZERO);
                        intermediate_logical_ts1755007871046 = intermediate_logical_ts1755007871046 || (inj_in_c_1755007871044_953 != CONST_ZERO);
                        inj_out_logical_1755007871044_281 = !intermediate_logical_ts1755007871046;
                        inj_out_unary_not_1755007871044_29 = ~inj_in_a_1755007871044_510;
                        inj_out_negate_1755007871044_562 = -inj_in_a_1755007871044_510;
                        intermediate_add_assoc_ts1755007871046 = (inj_in_a_1755007871044_510 + inj_in_b_1755007871044_514) + inj_in_c_1755007871044_953;
                        inj_out_add_assoc_1755007871044_492 = intermediate_add_assoc_ts1755007871046;
                        intermediate_mul_assoc_ts1755007871046 = (inj_in_a_1755007871044_510 * inj_in_b_1755007871044_514) * inj_in_c_1755007871044_953;
                        inj_out_mul_assoc_1755007871044_457 = intermediate_mul_assoc_ts1755007871046;
                        intermediate_and_assoc_ts1755007871046 = (inj_in_a_1755007871044_510 & inj_in_b_1755007871044_514) & inj_in_c_1755007871044_953;
                        inj_out_and_assoc_1755007871044_763 = intermediate_and_assoc_ts1755007871046;
                        intermediate_or_assoc_ts1755007871046 = (inj_in_a_1755007871044_510 | inj_in_b_1755007871044_514) | inj_in_c_1755007871044_953;
                        inj_out_or_assoc_1755007871044_226 = intermediate_or_assoc_ts1755007871046;
                        intermediate_xor_assoc_ts1755007871046 = (inj_in_a_1755007871044_510 ^ inj_in_b_1755007871044_514) ^ inj_in_c_1755007871044_953;
                        inj_out_xor_assoc_1755007871044_99 = intermediate_xor_assoc_ts1755007871046;
                        inj_out_and_swap_const_1755007871044_310 = inj_in_const1_1755007871044_785 & inj_in_a_1755007871044_510;
                        inj_out_or_swap_not_1755007871044_77 = (~inj_in_a_1755007871044_510) | inj_in_b_1755007871044_514;
                        inj_out_xor_swap_var_1755007871044_563 = inj_in_b_1755007871044_514 ^ inj_in_c_1755007871044_953;
                    end
                    // END: Mod_BasicOps_ts1755007871046

                    simple_undeclared_mod simple_undeclared_mod_inst_1755007871042_3698 (
                        .in_val(inj_val_a_1755007870999_375),
                        .out_val(inj_out_val_1755007871042_788)
                    );
                    mod_casez_wildcard mod_casez_wildcard_inst_1755007871041_2018 (
                        .in_mask_z(inj_in_mask_z_1755007871041_918),
                        .out_match_type_z(inj_out_match_type_z_1755007871041_40)
                    );
                    // BEGIN: child_packed_scalar_port_ts1755007871039
                    assign inj_data_out_1755007871039_65 = inj_val_b_1755007871004_723;
                    // END: child_packed_scalar_port_ts1755007871039

                    case_unique0_violating_mod case_unique0_violating_mod_inst_1755007871035_8370 (
                        .case_expr(inj_case_expr_1755007871035_636),
                        .internal_out(inj_internal_out_1755007871035_54)
                    );
                    attributes_on_expr_port attributes_on_expr_port_inst_1755007871032_4336 (
                        .o_out(inj_o_out_1755007871032_725),
                        .i_control(internal_state_ts1755007870998),
                        .i_in(inj_in2_1755007870997_556)
                    );
                always_comb begin
                    internal_ts1755007871029 = inj_in_val_m1_1755007870999_560;
                    inj_out_bits_1755007871029_205 = internal_ts1755007871029[3 -: 2];
                end
                // END: cast_select_demo_ts1755007871029

                // BEGIN: mod_named_begin_ts1755007871026
                always_comb begin : my_named_block
                    inj_data_out_1755007871026_735 = inj_val_a_1755007870999_375;
                end
                // END: mod_named_begin_ts1755007871026

                // BEGIN: GenerateFor_ts1755007871023
                genvar i;
                generate
                    for (i = 0; i < 4; i = i + 1) begin : g_loop
                        assign inj_data_out_1755007871023_101[i] = inj_val_b_1755007871004_723[i];
                    end
                endgenerate
                // END: GenerateFor_ts1755007871023

                split_if_empty_then split_if_empty_then_inst_1755007871020_1145 (
                    .in_val_p(inj_add_val_m1_1755007870999_860),
                    .out_reg_p(inj_out_reg_p_1755007871020_406),
                    .clk_p(clk),
                    .condition_p(internal_state_ts1755007870998)
                );
                range_select_indexed_packed range_select_indexed_packed_inst_1755007871018_2891 (
                    .width(inj_val_c_1755007870999_372),
                    .out_down(inj_out_down_1755007871018_688),
                    .out_up(inj_out_up_1755007871018_139),
                    .in_vec(inj_in_vec_1755007871018_632),
                    .start_index(inj_val_a_1755007870999_375)
                );
                // BEGIN: PragmaProtectOptions_ts1755007871016
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
            assign inj_config_data_out_1755007871016_220 = temp_val_ts1755007871012 + 1;
                // END: PragmaProtectOptions_ts1755007871016

                more_ops more_ops_inst_1755007871014_3141 (
                    .ored(inj_ored_1755007871014_402),
                    .sum(inj_sum_1755007871014_280),
                    .xored(inj_xored_1755007871014_100),
                    .a(var_m1_ts1755007871000),
                    .b(inj_in_val_m1_1755007870999_560),
                    .c(inj_add_val_m1_1755007870999_860),
                    .anded(inj_anded_1755007871014_897),
                    .diff(inj_diff_1755007871014_561)
                );
            update_val(inj_val_c_1755007870999_372, temp_val_ts1755007871012);
            inj_o_val_1755007871011_378 = temp_val_ts1755007871012;
        end
        // END: mod_automatic_task_ts1755007871012

        simple_assign simple_assign_inst_1755007871009_2389 (
            .in(inj_in_val_m1_1755007870999_560),
            .out(inj_out_1755007871009_727)
        );
        // BEGIN: SimpleAssign_ts1755007871008
        assign inj_val_out_1755007871008_11 = inj_val_in_1755007871008_78;
        // END: SimpleAssign_ts1755007871008

        module_packed_variables module_packed_variables_inst_1755007871006_8207 (
            .data_out_pa(inj_data_out_pa_1755007871006_215),
            .data_out_pv(inj_data_out_pv_1755007871006_698),
            .data_in_pa(inj_data_in_pa_1755007871006_600),
            .data_in_pv(inj_in_val_m1_1755007870999_560),
            .enable_pv(internal_state_ts1755007870998)
        );
        CombinationalLogic CombinationalLogic_inst_1755007871004_9527 (
            .enable(internal_state_ts1755007870998),
            .val_a(inj_in_vector_1755007870997_492),
            .val_b(inj_val_b_1755007871004_723),
            .result(inj_result_1755007871004_570)
        );
        // BEGIN: mod_event_implicit_ts1755007871003
        always @* begin
            inj_data_out_1755007871003_167 = inj_in0_1755007871001_64;
        end
        // END: mod_event_implicit_ts1755007871003

        // BEGIN: Comb_Case_ts1755007871001
        always_comb begin
            case (inj_sel_1755007871001_599)
                2'b00: inj_mux_out_1755007871001_438 = inj_in0_1755007871001_64;
                2'b01: inj_mux_out_1755007871001_438 = inj_in1_1755007871001_117;
                2'b10: inj_mux_out_1755007871001_438 = inj_in2_1755007871001_4;
                default: inj_mux_out_1755007871001_438 = inj_in3_1755007871001_785;
            endcase
        end
        // END: Comb_Case_ts1755007871001

    always_comb begin
        var_m1_ts1755007871000 = inj_in_val_m1_1755007870999_560;
        inj_out_sum_m1_1755007870999_891 = (++var_m1_ts1755007871000) + inj_add_val_m1_1755007870999_860;
        inj_var_out_m1_1755007870999_197 = var_m1_ts1755007871000;
    end
    // END: expr_preadd_comb_ts1755007871000

    dup_compare dup_compare_inst_1755007870999_8400 (
        .val_c(inj_val_c_1755007870999_372),
        .indicators(inj_indicators_1755007870999_327),
        .val_a(inj_val_a_1755007870999_375),
        .val_b(inj_val_b_1755007870999_772)
    );
`ifdef SLANG_PRAGMA
`protect begin
`endif
assign internal_state_ts1755007870998 = inj_in2_1755007870997_556;
`ifdef SLANG_PRAGMA
`protect end
`endif
`ifdef SLANG_PRAGMA
`protect begin_protected
`endif
`ifdef SLANG_PRAGMA
`protect end_protected
`endif
assign inj_protected_active_1755007870998_602 = internal_state_ts1755007870998;
    // END: PragmaProtectBoundaries_ts1755007870998

    always_comb begin
        inj_out1_1755007870997_113 = |inj_in1_1755007870997_890;
        inj_out2_1755007870997_239 = |inj_in2_1755007870997_556;
        inj_extra_out_1755007870997_455 = inj_out1_1755007870997_113 ^ inj_out2_1755007870997_239;
    end
    // END: ansi_implicit_inherit_ts1755007870997

    always_comb begin
        if (inj_in_vector_1755007870997_492 > 4'd5) begin
            inj_out_single_1755007870997_841 = 1'b1;
        end else begin
            inj_out_single_1755007870997_841 = 1'b0;
        end
    end
    // END: combinatorial_logic_ts1755007870997
endmodule

