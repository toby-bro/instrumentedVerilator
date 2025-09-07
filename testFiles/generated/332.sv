interface struct_if;
    logic [7:0] packet_field1;
    logic [7:0] packet_field2;
    logic tx_en;
    modport Access (output packet_field1, output packet_field2, output tx_en);
endinterface
module ModSimpleLogic (
    input logic a,
    input logic b,
    output logic y
);
    assign y = a ^ b;
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

module ModuleLineDirective (
    input logic in1,
    output logic out1
);
    logic internal_sig_a;
    logic internal_sig_b;
    logic unused_line_var;
    `line 100 "virtual_file_A.sv" 1
    assign internal_sig_a = in1;
    `line 20 "virtual_file_B.sv" 1
    assign internal_sig_b = ~internal_sig_a;
    assign unused_line_var = 1'b1;
    `line 150 "virtual_file_A.sv" 2
    assign out1 = internal_sig_b;
    `line 1 "original_file.sv" 0
endmodule

module Module_MacroTokens (
    input logic tok_in,
    output logic tok_out
);
    `define PASTE(a,b) a``b
    logic `PASTE(my,_var);
    always_comb begin
        `PASTE(my,_var) = tok_in;
        tok_out         = `PASTE(my,_var);
    end
endmodule

module Parameterized #(
    parameter int WIDTH = 8
) (
    input logic [7:0] din,
    output logic [7:0] dout
);
    assign dout = din;
endmodule

module ProgramDefinition (
    input wire in_pd,
    output logic out_pd
);
    assign out_pd = in_pd;
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

module explicit_non_ansi_decl_module (
    p_in,
    p_out
);
    input logic p_in;
    output wire p_out;
    assign p_out = p_in;
endmodule

module mod_internal_if_test (
    input wire in_i,
    output logic out_o
);
    assign out_o = !in_i;
endmodule

module split_for_loop (
    input logic clk_i,
    input logic [7:0] start_val_i,
    output logic [15:0] sum_out_i
);
    always @(posedge clk_i) begin
        sum_out_i <= 0;
        for (int i = 0; i < 4; i = i + 1) begin
            sum_out_i <= sum_out_i + start_val_i + i;
        end
    end
endmodule

module snippet (
    input wire clk,
    input int inj_b_1755007865758_389,
    input logic [3:0] inj_data_in_1755007865755_1,
    input logic [7:0] inj_data_in_k_1755007865754_687,
    input logic inj_enable_in_1755007865753_782,
    input wire [7:0] inj_in_a_1755007865763_851,
    input wire [7:0] inj_in_b_1755007865763_240,
    input wire inj_in_bit_1755007865763_655,
    input wire [7:0] inj_in_c_1755007865763_950,
    input wire inj_in_cond_1755007865763_203,
    input wire inj_in_cond_neq_rhs_1755007865763_719,
    input logic inj_in_h_1755007865753_609,
    input bit [3:0] inj_in_mask_x_1755007865757_77,
    input wire [7:0] inj_in_not_else_1755007865763_67,
    input wire [7:0] inj_in_not_then_1755007865763_943,
    input logic [7:0] inj_in_val_e_1755007865756_139,
    input logic [3:0] inj_val_a_1755007865766_295,
    input wire reset,
    output logic inj_data_out_1755007865753_642,
    output logic [3:0] inj_data_out_1755007865755_862,
    output logic [7:0] inj_data_out_k_1755007865754_268,
    output logic [7:0] inj_dout_1755007865759_865,
    output logic inj_out1_1755007865760_967,
    output logic inj_out_a_1755007865758_454,
    output int inj_out_b_1755007865758_853,
    output logic inj_out_c_1755007865761_808,
    output logic inj_out_eq_1755007865763_204,
    output logic inj_out_eq_concat_1755007865763_562,
    output logic inj_out_gt_1755007865763_700,
    output logic inj_out_gte_1755007865763_23,
    output logic inj_out_i_1755007865753_564,
    output logic inj_out_lt_1755007865763_455,
    output logic inj_out_lte_1755007865763_601,
    output bit [1:0] inj_out_match_type_x_1755007865757_845,
    output logic inj_out_neq_1755007865763_90,
    output logic inj_out_not_eq_1755007865763_839,
    output logic inj_out_not_neq_1755007865763_171,
    output logic inj_out_o_1755007865753_43,
    output logic inj_out_pd_1755007865762_525,
    output logic inj_out_ternary_1755007865763_882,
    output logic inj_out_ternary_1bit_0else_1755007865763_992,
    output logic inj_out_ternary_1bit_0then_1755007865763_770,
    output logic inj_out_ternary_1bit_1else_1755007865763_463,
    output logic inj_out_ternary_1bit_1then_1755007865763_823,
    output logic inj_out_ternary_const_cond_false_1755007865763_257,
    output logic inj_out_ternary_const_cond_true_1755007865763_714,
    output logic [7:0] inj_out_ternary_dec_1755007865763_479,
    output logic [7:0] inj_out_ternary_inc_1755007865763_258,
    output logic [7:0] inj_out_ternary_pulled_nots_1755007865763_580,
    output logic inj_out_ternary_swapped_cond_1755007865763_543,
    output logic inj_out_ternary_swapped_neq_cond_1755007865763_23,
    output logic [7:0] inj_out_val_e_1755007865756_565,
    output wire inj_p_out_1755007865755_702,
    output logic [3:0] inj_result_1755007865766_530,
    output logic inj_status_e_1755007865756_744,
    output logic inj_sum_1755007865765_266,
    output logic [15:0] inj_sum_out_i_1755007865762_382,
    output logic inj_tok_out_1755007865755_664,
    output logic inj_tx_status_1755007865757_688,
    output logic inj_y_1755007865756_203
);
    // BEGIN: LintAsyncFovIssue_ts1755007865753
    // BEGIN: sequential_register_ts1755007865754
    // BEGIN: split_input_only_var_ts1755007865754
    // BEGIN: GenerateFor_ts1755007865755
    genvar i;
    // BEGIN: split_mixed_cond_seq_ts1755007865756
    logic [7:0] temp_val_e_ts1755007865756;
        // BEGIN: ModuleBasic_ts1755007865758
        parameter int P1  = 10;
        localparam int LP1 = 20;
        logic c_ts1755007865758;
        int   d_ts1755007865758;
        always_comb begin
            logic temp_v_ts1755007865758;
                // BEGIN: CombinationalLogic_ts1755007865766
                always_comb begin
                    if (inj_enable_in_1755007865753_782) begin
                        inj_result_1755007865766_530 = inj_val_a_1755007865766_295 + inj_data_in_1755007865755_1;
                    end else begin
                        inj_result_1755007865766_530 = 4'h0;
                    end
                end
                // END: CombinationalLogic_ts1755007865766

                // BEGIN: simple_adder_ts1755007865765
                assign inj_sum_1755007865765_266 = temp_v_ts1755007865758 + inj_enable_in_1755007865753_782;
                // END: simple_adder_ts1755007865765

                Mod_TernaryLogic Mod_TernaryLogic_inst_1755007865763_5728 (
                    .out_ternary(inj_out_ternary_1755007865763_882),
                    .out_ternary_pulled_nots(inj_out_ternary_pulled_nots_1755007865763_580),
                    .in_b(inj_in_b_1755007865763_240),
                    .out_lt(inj_out_lt_1755007865763_455),
                    .in_cond_neq_lhs(reset),
                    .out_ternary_1bit_0then(inj_out_ternary_1bit_0then_1755007865763_770),
                    .in_cond(inj_in_cond_1755007865763_203),
                    .out_ternary_1bit_1else(inj_out_ternary_1bit_1else_1755007865763_463),
                    .in_not_then(inj_in_not_then_1755007865763_943),
                    .in_cond_not(clk),
                    .out_ternary_1bit_1then(inj_out_ternary_1bit_1then_1755007865763_823),
                    .in_c(inj_in_c_1755007865763_950),
                    .out_neq(inj_out_neq_1755007865763_90),
                    .out_not_neq(inj_out_not_neq_1755007865763_171),
                    .out_gt(inj_out_gt_1755007865763_700),
                    .out_ternary_const_cond_false(inj_out_ternary_const_cond_false_1755007865763_257),
                    .out_gte(inj_out_gte_1755007865763_23),
                    .out_ternary_inc(inj_out_ternary_inc_1755007865763_258),
                    .in_a(inj_in_a_1755007865763_851),
                    .in_cond_neq_rhs(inj_in_cond_neq_rhs_1755007865763_719),
                    .out_ternary_dec(inj_out_ternary_dec_1755007865763_479),
                    .out_eq_concat(inj_out_eq_concat_1755007865763_562),
                    .out_ternary_1bit_0else(inj_out_ternary_1bit_0else_1755007865763_992),
                    .out_ternary_swapped_cond(inj_out_ternary_swapped_cond_1755007865763_543),
                    .out_lte(inj_out_lte_1755007865763_601),
                    .out_not_eq(inj_out_not_eq_1755007865763_839),
                    .in_bit(inj_in_bit_1755007865763_655),
                    .out_ternary_const_cond_true(inj_out_ternary_const_cond_true_1755007865763_714),
                    .in_not_else(inj_in_not_else_1755007865763_67),
                    .out_eq(inj_out_eq_1755007865763_204),
                    .out_ternary_swapped_neq_cond(inj_out_ternary_swapped_neq_cond_1755007865763_23)
                );
                split_for_loop split_for_loop_inst_1755007865763_8542 (
                    .start_val_i(inj_in_val_e_1755007865756_139),
                    .sum_out_i(inj_sum_out_i_1755007865762_382),
                    .clk_i(clk)
                );
                ProgramDefinition ProgramDefinition_inst_1755007865762_3603 (
                    .in_pd(clk),
                    .out_pd(inj_out_pd_1755007865762_525)
                );
                basic_assign_if basic_assign_if_inst_1755007865761_8134 (
                    .out_c(inj_out_c_1755007865761_808),
                    .in_a(inj_in_h_1755007865753_609),
                    .in_b(inj_enable_in_1755007865753_782)
                );
                ModuleLineDirective ModuleLineDirective_inst_1755007865760_8502 (
                    .out1(inj_out1_1755007865760_967),
                    .in1(c_ts1755007865758)
                );
                Parameterized Parameterized_inst_1755007865759_220 (
                    .din(temp_val_e_ts1755007865756),
                    .dout(inj_dout_1755007865759_865)
                );
            temp_v_ts1755007865758 = d_ts1755007865758;
            c_ts1755007865758      = temp_v_ts1755007865758;
        end
        assign inj_out_a_1755007865758_454 = inj_in_h_1755007865753_609;
        assign d_ts1755007865758     = inj_b_1755007865758_389;
        assign inj_out_b_1755007865758_853 = d_ts1755007865758 + P1 + LP1;
        // END: ModuleBasic_ts1755007865758

        // BEGIN: mod_casex_wildcard_overlap_priority_ts1755007865757
    always_comb begin
        inj_out_match_type_x_1755007865757_845 = 2'b01;
        priority casex (inj_in_mask_x_1755007865757_77)
            4'b1X0Z: begin
                inj_out_match_type_x_1755007865757_845 = 2'b10;
            end
            4'b10?Z: begin
                inj_out_match_type_x_1755007865757_845 = 2'b11;
            end
            4'bZ1?X: begin
                inj_out_match_type_x_1755007865757_845 = 2'b00;
            end
            default: begin
                inj_out_match_type_x_1755007865757_845 = 2'b01;
            end
        endcase
    end
        // END: mod_casex_wildcard_overlap_priority_ts1755007865757

        // BEGIN: module_struct_write_ts1755007865757
        struct_if stif_inst();
        always_comb begin
            stif_inst.packet_field1 = inj_in_val_e_1755007865756_139;
            stif_inst.packet_field2 = inj_data_in_k_1755007865754_687;
            stif_inst.tx_en = 1'b1;
            inj_tx_status_1755007865757_688 = stif_inst.tx_en;
        end
        // END: module_struct_write_ts1755007865757

    always @(posedge clk) begin
        temp_val_e_ts1755007865756 <= inj_in_val_e_1755007865756_139 + 5;
        if (inj_in_h_1755007865753_609) begin
            inj_out_val_e_1755007865756_565 <= temp_val_e_ts1755007865756;
            inj_status_e_1755007865756_744 <= 1;
        end else begin
            inj_out_val_e_1755007865756_565 <= inj_data_in_k_1755007865754_687;
            inj_status_e_1755007865756_744 <= 0;
        end
    end
    // END: split_mixed_cond_seq_ts1755007865756

    ModSimpleLogic ModSimpleLogic_inst_1755007865756_2234 (
        .a(inj_in_h_1755007865753_609),
        .b(inj_enable_in_1755007865753_782),
        .y(inj_y_1755007865756_203)
    );
    explicit_non_ansi_decl_module explicit_non_ansi_decl_module_inst_1755007865755_8349 (
        .p_in(inj_in_h_1755007865753_609),
        .p_out(inj_p_out_1755007865755_702)
    );
    generate
        for (i = 0; i < 4; i = i + 1) begin : g_loop
            assign inj_data_out_1755007865755_862[i] = inj_data_in_1755007865755_1[i];
        end
    endgenerate
    // END: GenerateFor_ts1755007865755

    Module_MacroTokens Module_MacroTokens_inst_1755007865755_9737 (
        .tok_in(inj_enable_in_1755007865753_782),
        .tok_out(inj_tok_out_1755007865755_664)
    );
    always @(posedge clk) begin
        if (inj_in_h_1755007865753_609) begin
            inj_data_out_k_1755007865754_268 <= inj_data_in_k_1755007865754_687;
        end
    end
    // END: split_input_only_var_ts1755007865754

    always_ff @(posedge clk or negedge reset) begin
        if (!reset) begin
            inj_data_out_1755007865753_642 <= 1'b0; 
        end else if (inj_enable_in_1755007865753_782) begin
            inj_data_out_1755007865753_642 <= inj_in_h_1755007865753_609; 
        end
    end
    // END: sequential_register_ts1755007865754

    always_ff @(posedge clk or negedge reset) begin
        if (!reset) begin
            inj_out_i_1755007865753_564 <= 1'b0;
        end else begin
            inj_out_i_1755007865753_564 <= inj_in_h_1755007865753_609 & inj_out_i_1755007865753_564;
        end
    end
    // END: LintAsyncFovIssue_ts1755007865753

    mod_internal_if_test mod_internal_if_test_inst_1755007865753_3401 (
        .in_i(reset),
        .out_o(inj_out_o_1755007865753_43)
    );
endmodule

