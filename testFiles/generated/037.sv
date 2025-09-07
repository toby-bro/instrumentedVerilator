interface seq2_if;
    logic [7:0] status_byte;
    modport PortB (output status_byte);
endinterface
interface seq_if;
    logic [31:0] value_a;
    modport PortA (output value_a);
endinterface
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

module ModuleFF (
    input logic clk,
    input bit [3:0] in1,
    input bit [3:0] in2,
    input logic reset,
    output bit [3:0] out1,
    output bit [3:0] out2
);
    parameter int MAX_COUNT = 10;
    localparam int START_VAL = 5;
    logic [3:0] ff_reg;
    integer unused_int_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            ff_reg <= START_VAL;
            out1 <= '0;
            out2 <= '0;
            unused_int_var <= 0;
        end else begin
            case ({in1, in2})
                8'h00: ff_reg <= ff_reg;
                8'h01: ff_reg <= in1 + in2;
                default: ff_reg <= MAX_COUNT;
            endcase
            out1 <= ff_reg;
            out2 <= {in1[0], in1[0], in1[0], in1[0]} | {in2[3], in2[2], in2[1], in2[0]};
        end
    end
endmodule

module ReductionOperations (
    input logic [7:0] data_in,
    output logic and_reduce,
    output logic or_reduce,
    output logic xor_reduce
);
    assign and_reduce = &data_in;
    assign or_reduce = |data_in;
    assign xor_reduce = ^data_in;
endmodule

module child_empty_ports (
    p1,
    p2
);
    input logic p1;
    output logic p2;
    assign p2 = p1;
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

module mod_part_select (
    input wire [31:0] data_in,
    output logic [31:0] data_out
);
    logic [31:0] temp_reg;
    always_comb begin
        temp_reg[7:0] = data_in[7:0];
        temp_reg[15:8] = data_in[23:16];
        temp_reg[31:16] = data_in[15:0];
        temp_reg[0] = data_in[31];
        temp_reg[8] = data_in[0];
        data_out = temp_reg;
    end
endmodule

module mod_seq_reg (
    input logic clk,
    input logic d,
    output logic q
);
    always_ff @(posedge clk) begin
        q <= d;
    end
endmodule

module module_in_program_ref (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module param_local_port #(
    parameter int P_PORT_VAL = 25
) (
    input logic i_reset,
    output logic [7:0] o_sum
);
    localparam int LP_BODY_VAL = 125;
    localparam int LP_CALCULATED = P_PORT_VAL + LP_BODY_VAL;
    always_comb begin
        if (i_reset) begin
            o_sum = 0;
        end else begin
            o_sum = LP_CALCULATED;
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

module sequential_register_en (
    input logic clk,
    input logic [7:0] data_in,
    input logic en,
    output logic [7:0] data_out
);
    always_ff @(posedge clk) begin
        if (en) begin
            data_out <= data_in;
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

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module snippet #(
    parameter int P_PORT_VAL = 25
) (
    input wire clk,
    input bit [7:0] inj_data1_1755007763134_0,
    input bit [7:0] inj_data2_1755007763134_612,
    input wire [31:0] inj_data_in_1755007763072_231,
    input logic [3:0] inj_data_in_n_1755007763055_701,
    input logic inj_enable_in_1755007763162_713,
    input wire [7:0] inj_in1_1755007763052_463,
    input bit [3:0] inj_in1_1755007763060_715,
    input logic [2:0] inj_in1_1755007763067_714,
    input wire [7:0] inj_in2_1755007763052_799,
    input bit [3:0] inj_in2_1755007763060_678,
    input wire [7:0] inj_in_a_1755007763142_580,
    input logic [7:0] inj_in_a_g_1755007763051_41,
    input logic [7:0] inj_in_b_g_1755007763051_846,
    input wire inj_in_bit_1755007763142_150,
    input wire [7:0] inj_in_c_1755007763142_766,
    input wire inj_in_cond_neq_lhs_1755007763142_591,
    input wire inj_in_cond_neq_rhs_1755007763142_852,
    input bit inj_in_h_1755007763104_371,
    input wire [2:0] inj_in_index_1755007763057_132,
    input wire [7:0] inj_in_not_else_1755007763142_135,
    input wire [1:0] inj_in_part_lsb_1755007763057_523,
    input bit [2:0] inj_in_state_case_1755007763097_87,
    input int inj_in_val_1755007763066_939,
    input logic [31:0] inj_p_in1_1755007763051_853,
    input logic [31:0] inj_p_in2_1755007763051_274,
    input logic [1:0] inj_p_mode_1755007763051_491,
    input logic inj_start_task_1755007763053_312,
    input wire reset,
    output logic inj_and_reduce_1755007763215_329,
    output logic [7:0] inj_data_a_out_task_1755007763053_651,
    output logic [7:0] inj_data_b_out_task_1755007763053_48,
    output logic [3:0] inj_data_out1_n_1755007763055_945,
    output logic [3:0] inj_data_out2_n_1755007763055_0,
    output logic [31:0] inj_data_out_1755007763072_615,
    output logic [7:0] inj_data_out_1755007763078_187,
    output logic [3:0] inj_data_out_1755007763118_58,
    output logic inj_data_out_1755007763162_553,
    output logic [7:0] inj_default_out_1755007763071_921,
    output logic inj_extra_out_1755007763067_19,
    output logic [4:0] inj_internal_out_1755007763082_698,
    output logic [4:0] inj_internal_out_1755007763194_636,
    output logic [7:0] inj_o_sum_1755007763064_991,
    output logic [7:0] inj_o_sum_1755007763087_616,
    output logic [7:0] inj_o_target_result_1755007763062_515,
    output logic inj_or_reduce_1755007763215_94,
    output wire [7:0] inj_out1_1755007763052_160,
    output bit [3:0] inj_out1_1755007763060_142,
    output logic inj_out1_1755007763067_737,
    output logic inj_out1_bind_def_1755007763112_380,
    output wire [7:0] inj_out2_1755007763052_312,
    output bit [3:0] inj_out2_1755007763060_198,
    output logic inj_out2_1755007763067_386,
    output logic inj_out_bit_select_1755007763057_784,
    output logic [7:0] inj_out_bitwise_ops_1755007763057_165,
    output logic inj_out_eq_1755007763142_652,
    output logic inj_out_eq_concat_1755007763142_97,
    output logic inj_out_gt_1755007763142_186,
    output logic inj_out_gte_1755007763142_952,
    output logic inj_out_h_1755007763104_100,
    output logic inj_out_lt_1755007763142_990,
    output logic inj_out_lte_1755007763142_38,
    output logic inj_out_neq_1755007763142_533,
    output logic inj_out_not_eq_1755007763142_956,
    output logic inj_out_not_neq_1755007763142_635,
    output logic [7:0] inj_out_p_g_1755007763051_137,
    output logic [3:0] inj_out_part_select_1755007763057_653,
    output bit inj_out_priority_case_1755007763097_590,
    output logic [7:0] inj_out_q_g_1755007763051_724,
    output logic [7:0] inj_out_reg_a_1755007763074_728,
    output logic [7:0] inj_out_reg_b_1755007763074_644,
    output logic inj_out_ternary_1755007763142_318,
    output logic inj_out_ternary_1bit_0else_1755007763142_653,
    output logic inj_out_ternary_1bit_0then_1755007763142_441,
    output logic inj_out_ternary_1bit_1else_1755007763142_940,
    output logic inj_out_ternary_1bit_1then_1755007763142_213,
    output logic inj_out_ternary_const_cond_false_1755007763142_869,
    output logic inj_out_ternary_const_cond_true_1755007763142_535,
    output logic [7:0] inj_out_ternary_dec_1755007763142_777,
    output logic [7:0] inj_out_ternary_inc_1755007763142_152,
    output logic [7:0] inj_out_ternary_pulled_nots_1755007763142_215,
    output logic inj_out_ternary_swapped_cond_1755007763142_81,
    output logic inj_out_ternary_swapped_neq_cond_1755007763142_447,
    output bit inj_out_unique_case_1755007763097_737,
    output int inj_out_val_1755007763066_743,
    output logic [31:0] inj_out_val_1755007763125_68,
    output int inj_out_val_1755007763152_720,
    output logic [7:0] inj_out_vec_y_1755007763204_319,
    output logic [7:0] inj_out_vector_assign_1755007763057_197,
    output logic inj_p2_1755007763063_650,
    output logic [31:0] inj_p_out_1755007763051_108,
    output logic inj_q_1755007763069_553,
    output bit [7:0] inj_result1_1755007763134_413,
    output bit [7:0] inj_result2_1755007763134_576,
    output logic inj_sequence_valid_1755007763172_222,
    output logic inj_sub_out_1755007763182_82,
    output logic [7:0] inj_x_aa_1755007763092_323,
    output logic inj_xor_reduce_1755007763215_908,
    output logic [7:0] inj_y_aa_1755007763092_619,
    output logic [7:0] inj_z_aa_1755007763092_112
);
    // BEGIN: more_procedural_ts1755007763051
    // BEGIN: split_reorder_blocking_ts1755007763051
    logic [7:0] mid_x_g_ts1755007763051;
    logic [7:0] mid_y_g_ts1755007763051;
        // BEGIN: multi_always_comb_ts1755007763052
        logic [7:0] intermediate1_ts1755007763052;
        logic [7:0] intermediate2_ts1755007763052;
            // BEGIN: module_task_args_ts1755007763054
            logic [7:0] data_a_ts1755007763053 ;
            logic [7:0] data_b_ts1755007763053 ;
                // BEGIN: split_multiple_blocking_ts1755007763055
                logic [3:0] temp_n_ts1755007763055;
                    // BEGIN: mod_split_ff_ts1755007763074
                    logic [7:0]  split_reg_var_ts1755007763074;
                    logic [7:0] other_reg_var_ts1755007763074;
                        // BEGIN: sequential_logic_ts1755007763119
                        ;
                        logic [3:0] internal_reg_ts1755007763119;
                            ReductionOperations ReductionOperations_inst_1755007763215_9397 (
                                .data_in(other_reg_var_ts1755007763074),
                                .and_reduce(inj_and_reduce_1755007763215_329),
                                .or_reduce(inj_or_reduce_1755007763215_94),
                                .xor_reduce(inj_xor_reduce_1755007763215_908)
                            );
                            split_vector_assign split_vector_assign_inst_1755007763204_668 (
                                .clk_y(clk),
                                .condition_y(inj_enable_in_1755007763162_713),
                                .in_val_y(data_a_ts1755007763053),
                                .out_vec_y(inj_out_vec_y_1755007763204_319)
                            );
                            // BEGIN: case_full_parallel_mod_ts1755007763194
                            always @* begin
                                (* full, parallel *)
                                case (inj_p_mode_1755007763051_491)
                                    2'b00: inj_internal_out_1755007763194_636 = 1;
                                    2'b01: inj_internal_out_1755007763194_636 = 2;
                                    2'b10: inj_internal_out_1755007763194_636 = 3;
                                    default: inj_internal_out_1755007763194_636 = 4;
                                endcase
                            end
                            // END: case_full_parallel_mod_ts1755007763194

                            // BEGIN: sub_module_ts1755007763182
                            assign inj_sub_out_1755007763182_82 = !inj_start_task_1755007763053_312;
                            // END: sub_module_ts1755007763182

                            // BEGIN: module_sequence_different_if_ts1755007763172
                            seq_if sif_port();
                            seq2_if sif2_port();
                            always_comb begin
                                sif_port.value_a = inj_p_in2_1755007763051_274;
                                sif2_port.status_byte = other_reg_var_ts1755007763074;
                                inj_sequence_valid_1755007763172_222 = 1'b1;
                            end
                            // END: module_sequence_different_if_ts1755007763172

                            sequential_register sequential_register_inst_1755007763162_3904 (
                                .enable_in(inj_enable_in_1755007763162_713),
                                .reset_n(reset),
                                .data_out(inj_data_out_1755007763162_553),
                                .clk(clk),
                                .data_in(inj_start_task_1755007763053_312)
                            );
                            module_in_program_ref module_in_program_ref_inst_1755007763152_2290 (
                                .in_val(inj_in_val_1755007763066_939),
                                .out_val(inj_out_val_1755007763152_720)
                            );
                            Mod_TernaryLogic Mod_TernaryLogic_inst_1755007763142_3387 (
                                .out_ternary_dec(inj_out_ternary_dec_1755007763142_777),
                                .out_eq_concat(inj_out_eq_concat_1755007763142_97),
                                .in_cond_neq_rhs(inj_in_cond_neq_rhs_1755007763142_852),
                                .in_not_then(inj_in2_1755007763052_799),
                                .in_not_else(inj_in_not_else_1755007763142_135),
                                .in_bit(inj_in_bit_1755007763142_150),
                                .out_gte(inj_out_gte_1755007763142_952),
                                .in_cond_not(clk),
                                .out_not_neq(inj_out_not_neq_1755007763142_635),
                                .out_ternary_const_cond_true(inj_out_ternary_const_cond_true_1755007763142_535),
                                .out_not_eq(inj_out_not_eq_1755007763142_956),
                                .in_a(inj_in_a_1755007763142_580),
                                .out_ternary_1bit_1then(inj_out_ternary_1bit_1then_1755007763142_213),
                                .out_ternary_1bit_0then(inj_out_ternary_1bit_0then_1755007763142_441),
                                .in_cond(reset),
                                .in_cond_neq_lhs(inj_in_cond_neq_lhs_1755007763142_591),
                                .out_gt(inj_out_gt_1755007763142_186),
                                .out_lt(inj_out_lt_1755007763142_990),
                                .in_c(inj_in_c_1755007763142_766),
                                .out_ternary(inj_out_ternary_1755007763142_318),
                                .in_b(inj_in1_1755007763052_463),
                                .out_lte(inj_out_lte_1755007763142_38),
                                .out_ternary_swapped_neq_cond(inj_out_ternary_swapped_neq_cond_1755007763142_447),
                                .out_ternary_const_cond_false(inj_out_ternary_const_cond_false_1755007763142_869),
                                .out_ternary_inc(inj_out_ternary_inc_1755007763142_152),
                                .out_ternary_1bit_1else(inj_out_ternary_1bit_1else_1755007763142_940),
                                .out_eq(inj_out_eq_1755007763142_652),
                                .out_ternary_swapped_cond(inj_out_ternary_swapped_cond_1755007763142_81),
                                .out_neq(inj_out_neq_1755007763142_533),
                                .out_ternary_pulled_nots(inj_out_ternary_pulled_nots_1755007763142_215),
                                .out_ternary_1bit_0else(inj_out_ternary_1bit_0else_1755007763142_653)
                            );
                            comb_conditional comb_conditional_inst_1755007763135_4689 (
                                .result2(inj_result2_1755007763134_576),
                                .data1(inj_data1_1755007763134_0),
                                .data2(inj_data2_1755007763134_612),
                                .sel(inj_in_h_1755007763104_371),
                                .result1(inj_result1_1755007763134_413)
                            );
                            // BEGIN: member_access_packed_union_ts1755007763126
                            typedef union packed {
                                logic [31:0] a_ts1755007763126; 
                                logic [31:0] b_ts1755007763126; 
                            } my_packed_union;
                            my_packed_union union_var;
                            always_comb begin
                                if (inj_in_h_1755007763104_371)
                                    union_var.a_ts1755007763126 = inj_p_in2_1755007763051_274;
                                else
                                    union_var.b_ts1755007763126 = inj_p_in2_1755007763051_274[31:0];
                                inj_out_val_1755007763125_68 = union_var.a_ts1755007763126;
                            end
                            // END: member_access_packed_union_ts1755007763126

                        always_ff @(posedge clk or negedge reset) begin
                            if (!reset) begin
                                internal_reg_ts1755007763119 <= 4'h0;
                            end else begin
                                internal_reg_ts1755007763119 <= temp_n_ts1755007763055;
                            end
                        end
                        assign inj_data_out_1755007763118_58 = internal_reg_ts1755007763119;
                        // END: sequential_logic_ts1755007763119

                        // BEGIN: mod_basic_bind_ts1755007763112
                        assign inj_out1_bind_def_1755007763112_380 = ~inj_start_task_1755007763053_312;
                        // END: mod_basic_bind_ts1755007763112

                        // BEGIN: CoverageHelper_ts1755007763104
                        assign inj_out_h_1755007763104_100 = inj_in_h_1755007763104_371;
                        // END: CoverageHelper_ts1755007763104

                        // BEGIN: mod_case_unique_priority_ts1755007763098
                    always_comb begin
                        inj_out_unique_case_1755007763097_737 = 1'b0;
                        unique case (inj_in_state_case_1755007763097_87)
                            3'd0: inj_out_unique_case_1755007763097_737 = 1'b0;
                            3'd1: inj_out_unique_case_1755007763097_737 = 1'b1;
                            3'd2: inj_out_unique_case_1755007763097_737 = 1'b0;
                            3'd1: inj_out_unique_case_1755007763097_737 = 1'b1;
                            default: inj_out_unique_case_1755007763097_737 = 1'b1;
                        endcase
                    end
                    always_comb begin
                        inj_out_priority_case_1755007763097_590 = 1'b0;
                        priority case (inj_in_state_case_1755007763097_87)
                            3'd0: inj_out_priority_case_1755007763097_590 = 1'b0;
                            3'd1: inj_out_priority_case_1755007763097_590 = 1'b1;
                            3'd2: inj_out_priority_case_1755007763097_590 = 1'b0;
                            3'd1: inj_out_priority_case_1755007763097_590 = 1'b1;
                            default: inj_out_priority_case_1755007763097_590 = 1'b1;
                        endcase
                    end
                        // END: mod_case_unique_priority_ts1755007763098

                        // BEGIN: split_combo_blocking_ts1755007763092
                        always @(*) begin
                            inj_x_aa_1755007763092_323 = split_reg_var_ts1755007763074 + data_b_ts1755007763053;
                            inj_y_aa_1755007763092_619 = inj_x_aa_1755007763092_323 - inj_in_a_g_1755007763051_41;
                            inj_z_aa_1755007763092_112 = split_reg_var_ts1755007763074 * inj_in_a_g_1755007763051_41;
                        end
                        // END: split_combo_blocking_ts1755007763092

                        param_local_port param_local_port_inst_1755007763087_3796 (
                            .i_reset(reset),
                            .o_sum(inj_o_sum_1755007763087_616)
                        );
                        // BEGIN: case_priority_casex_complex_mod_ts1755007763082
                        always @* begin
                            priority casex ({inj_p_mode_1755007763051_491, temp_n_ts1755007763055[1:0]})
                                4'b1???: inj_internal_out_1755007763082_698 = 24;
                                4'b?1??: inj_internal_out_1755007763082_698 = 25;  
                                4'b??1?: inj_internal_out_1755007763082_698 = 26;  
                                4'b???1: inj_internal_out_1755007763082_698 = 27;  
                                4'b0000: inj_internal_out_1755007763082_698 = 28;  
                                default: inj_internal_out_1755007763082_698 = 29;
                            endcase
                        end
                        // END: case_priority_casex_complex_mod_ts1755007763082

                        sequential_register_en sequential_register_en_inst_1755007763078_8700 (
                            .data_in(other_reg_var_ts1755007763074),
                            .en(inj_start_task_1755007763053_312),
                            .data_out(inj_data_out_1755007763078_187),
                            .clk(clk)
                        );
                    always_ff @(posedge clk or posedge reset) begin
                        if (reset) begin
                            split_reg_var_ts1755007763074 <= 8'b0;
                            other_reg_var_ts1755007763074 <= 8'b0;
                            inj_out_reg_a_1755007763074_728 <= 8'b0;
                            inj_out_reg_b_1755007763074_644 <= 8'b0;
                        end else begin
                            split_reg_var_ts1755007763074 <= intermediate2_ts1755007763052;
                            other_reg_var_ts1755007763074 <= intermediate2_ts1755007763052 + 2;
                            inj_out_reg_a_1755007763074_728 <= split_reg_var_ts1755007763074;
                            inj_out_reg_b_1755007763074_644 <= other_reg_var_ts1755007763074;
                        end
                    end
                    // END: mod_split_ff_ts1755007763074

                    mod_part_select mod_part_select_inst_1755007763072_3636 (
                        .data_in(inj_data_in_1755007763072_231),
                        .data_out(inj_data_out_1755007763072_615)
                    );
                    func_macro_defaults func_macro_defaults_inst_1755007763071_4004 (
                        .en(inj_start_task_1755007763053_312),
                        .default_out(inj_default_out_1755007763071_921)
                    );
                    mod_seq_reg mod_seq_reg_inst_1755007763069_4003 (
                        .q(inj_q_1755007763069_553),
                        .clk(clk),
                        .d(inj_start_task_1755007763053_312)
                    );
                    // BEGIN: ansi_implicit_inherit_ts1755007763067
                    always_comb begin
                        inj_out1_1755007763067_737 = |inj_in1_1755007763067_714;
                        inj_out2_1755007763067_386 = |inj_start_task_1755007763053_312;
                        inj_extra_out_1755007763067_19 = inj_out1_1755007763067_737 ^ inj_out2_1755007763067_386;
                    end
                    // END: ansi_implicit_inherit_ts1755007763067

                    // BEGIN: definition_used_diag_mod_ts1755007763066
                    assign inj_out_val_1755007763066_743 = inj_in_val_1755007763066_939;
                    // END: definition_used_diag_mod_ts1755007763066

                    // BEGIN: param_local_port_ts1755007763064
                    localparam int LP_BODY_VAL = 125;
                    localparam int LP_CALCULATED = P_PORT_VAL + LP_BODY_VAL;
                    always_comb begin
                        if (reset) begin
                            inj_o_sum_1755007763064_991 = 0;
                        end else begin
                            inj_o_sum_1755007763064_991 = LP_CALCULATED;
                        end
                    end
                    // END: param_local_port_ts1755007763064

                    child_empty_ports child_empty_ports_inst_1755007763063_8841 (
                        .p2(inj_p2_1755007763063_650),
                        .p1(inj_start_task_1755007763053_312)
                    );
                    target_module_for_bind target_module_for_bind_inst_1755007763062_6570 (
                        .i_target_clk(clk),
                        .i_target_data(inj_in_b_g_1755007763051_846),
                        .o_target_result(inj_o_target_result_1755007763062_515)
                    );
                    ModuleFF ModuleFF_inst_1755007763060_936 (
                        .in1(inj_in1_1755007763060_715),
                        .in2(inj_in2_1755007763060_678),
                        .reset(reset),
                        .out1(inj_out1_1755007763060_142),
                        .out2(inj_out2_1755007763060_198),
                        .clk(clk)
                    );
                    // BEGIN: module_selection_ts1755007763057
                    always_comb begin
                    inj_out_vector_assign_1755007763057_197 = inj_in1_1755007763052_463;
                    inj_out_bit_select_1755007763057_784 = inj_in1_1755007763052_463[inj_in_index_1755007763057_132];
                    inj_out_part_select_1755007763057_653 = inj_in1_1755007763052_463[inj_in_part_lsb_1755007763057_523 +: 4];
                    inj_out_bitwise_ops_1755007763057_165 = inj_in1_1755007763052_463 & {8{reset}};
                    end
                    // END: module_selection_ts1755007763057

                always @(*) begin
                    temp_n_ts1755007763055 = inj_data_in_n_1755007763055_701 + 1;
                    inj_data_out1_n_1755007763055_945 = temp_n_ts1755007763055 * 2;
                    inj_data_out2_n_1755007763055_0 = temp_n_ts1755007763055 + 3;
                end
                // END: split_multiple_blocking_ts1755007763055

            task automatic modify_vars;
                input logic [7:0] task_arg_ts1755007763053;
                logic [7:0] task_local_ts1755007763053 ;
                begin
                    task_local_ts1755007763053 = task_arg_ts1755007763053;
                    data_a_ts1755007763053 = task_local_ts1755007763053 + 8'd1;
                    data_b_ts1755007763053 = task_arg_ts1755007763053 - 8'd1;
                end
            endtask
            always_comb begin
                if (inj_start_task_1755007763053_312) begin
                    data_a_ts1755007763053 = mid_y_g_ts1755007763051;
                    data_b_ts1755007763053 = 8'hFF;
                    modify_vars(inj_in_b_g_1755007763051_846);
                end else begin
                    data_a_ts1755007763053 = 8'h00;
                    data_b_ts1755007763053 = 8'h00;
                end
            end
            always_comb begin
                inj_data_a_out_task_1755007763053_651 = data_a_ts1755007763053 + 8'd2;
                inj_data_b_out_task_1755007763053_48 = data_b_ts1755007763053;
            end
            // END: module_task_args_ts1755007763054

        always @(*) begin
            intermediate1_ts1755007763052 = inj_in1_1755007763052_463 & inj_in2_1755007763052_799;
        end
        always @(*) begin
            intermediate2_ts1755007763052 = inj_in1_1755007763052_463 | inj_in2_1755007763052_799;
        end
        assign inj_out1_1755007763052_160 = intermediate1_ts1755007763052 + 8'd1;
        assign inj_out2_1755007763052_312 = intermediate2_ts1755007763052 - 8'd1;
        // END: multi_always_comb_ts1755007763052

    always @(*) begin
        mid_x_g_ts1755007763051 = inj_in_a_g_1755007763051_41 * 2;
        mid_y_g_ts1755007763051 = mid_x_g_ts1755007763051 + inj_in_b_g_1755007763051_846;
        inj_out_p_g_1755007763051_137 = mid_y_g_ts1755007763051 - 1;
        inj_out_q_g_1755007763051_724 = mid_x_g_ts1755007763051 / 2;
    end
    // END: split_reorder_blocking_ts1755007763051

    always_comb begin
        case (inj_p_mode_1755007763051_491)
            2'b00: inj_p_out_1755007763051_108 = (inj_p_in1_1755007763051_853 + inj_p_in2_1755007763051_274) * 2;
            2'b01: inj_p_out_1755007763051_108 = (inj_p_in1_1755007763051_853 - inj_p_in2_1755007763051_274) / 3; 
            2'b10: inj_p_out_1755007763051_108 = (inj_p_in1_1755007763051_853 << 4) | (inj_p_in2_1755007763051_274 >> 2);
            default: inj_p_out_1755007763051_108 = ~(inj_p_in1_1755007763051_853 ^ inj_p_in2_1755007763051_274) + 1;
        endcase
    end
    // END: more_procedural_ts1755007763051
endmodule

