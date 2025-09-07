module Comb_IfElse (
    input wire condition,
    input wire [15:0] value1,
    input wire [15:0] value2,
    output reg [15:0] result_val
);
    always_comb begin
        if (condition) begin
            result_val = value1;
        end else begin
            result_val = value2;
        end
    end
endmodule

module FunctionTaskMod (
    input logic [7:0] data_in,
    output logic is_even
);
    function automatic bit check_even(input logic [7:0] v);
        check_even = ~v[0];
    endfunction
    task automatic dummy_task(input logic [7:0] v);
        int tmp;
        tmp = v;
    endtask
    assign is_even = check_even(data_in);
endmodule

module child_concat_output (
    input logic dummy_in,
    output logic [7:0] data
);
    assign data = dummy_in ? 8'hAA : 8'h55;
endmodule

module constant_sel (
    input logic [31:0] in,
    output logic [7:0] out1,
    output logic out2
);
    assign out1 = in[15:8];
    assign out2 = in[3];
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755007845810_982,
    input bit inj_in_1755007845807_18,
    input logic [31:0] inj_in_1755007845812_742,
    input bit [3:0] inj_in_data_1755007845820_672,
    input logic [2:0] inj_in_val_1755007845807_91,
    input logic [7:0] inj_in_val_1755007845808_930,
    input int inj_in_val_1755007845809_372,
    input logic [1:0] inj_large_data_in_1755007845811_216,
    input wire [15:0] inj_value1_1755007845814_81,
    input wire [15:0] inj_value2_1755007845814_16,
    input wire reset,
    output logic [7:0] inj_data_1755007845824_538,
    output bit inj_dummy_out_1755007845807_220,
    output logic [4:0] inj_internal_out_1755007845816_659,
    output logic inj_is_even_1755007845810_881,
    output logic [7:0] inj_large_sum_out_1755007845811_409,
    output logic [7:0] inj_out1_1755007845812_241,
    output logic [7:0] inj_out1_1755007845833_320,
    output logic inj_out2_1755007845812_97,
    output bit inj_out_1755007845807_850,
    output logic inj_out_a_1755007845810_880,
    output int inj_out_b_1755007845810_828,
    output logic inj_out_cmp_1755007845808_428,
    output logic inj_out_e_1755007845817_920,
    output logic inj_out_logic_1755007845819_848,
    output logic [7:0] inj_out_ops_1755007845808_521,
    output logic [3:0] inj_out_part_1755007845808_467,
    output logic [7:0] inj_out_q_1755007845809_794,
    output logic [7:0] inj_out_reg_1755007845808_639,
    output reg inj_out_res_1755007845807_886,
    output reg inj_out_res_1755007845840_196,
    output bit [3:0] inj_out_result_1755007845820_265,
    output int inj_out_val_1755007845809_97,
    output logic [7:0] inj_out_val_e_1755007845813_125,
    output logic [7:0] inj_out_vec_y_1755007845828_846,
    output reg [15:0] inj_result_val_1755007845814_697,
    output logic inj_status_e_1755007845813_134
);
    // BEGIN: casez_xz_alt_ts1755007845807
    // BEGIN: BindSimpleModule_ts1755007845807
    // BEGIN: module_finish_numbers_ts1755007845807
    parameter p_finish_0 = 0;
    parameter p_finish_1 = 1;
    parameter p_finish_2 = 2;
    parameter p_finish_other_3 = 3;
    parameter p_finish_large_100 = 100;
    parameter p_finish_neg_minus1 = -1;
    localparam lp_finish_0 = 0;
    localparam lp_finish_1 = 1;
    localparam lp_finish_2 = 2;
    localparam lp_finish_other_5 = 5;
    localparam lp_finish_neg_minus10 = -10;
    // BEGIN: module_assignments_in_loops_ts1755007845808
    localparam int PART_START = 4;
    localparam int PART_WIDTH = 4;
    logic [7:0] reg_var_ts1755007845808;
    logic [3:0] part_var_ts1755007845808;
        // BEGIN: Module_BasicSyntax_ts1755007845808
        logic [7:0] temp_ts1755007845808;
            // BEGIN: ModuleBasic_ts1755007845810
            parameter int P1  = 10;
            localparam int LP1 = 20;
            logic c_ts1755007845810;
            int   d_ts1755007845810;
            always_comb begin
                logic temp_v_ts1755007845810;
                    // BEGIN: loop_unroll_limit_test_ts1755007845811
                    logic [7:0] current_large_sum_ts1755007845811;
                        // BEGIN: split_mixed_cond_seq_ts1755007845813
                        logic [7:0] temp_val_e_ts1755007845813;
                            // BEGIN: dup_logic_ops_ts1755007845834
                            logic cond1_ts1755007845834, cond2_ts1755007845834, cond3_ts1755007845834;
                            logic complex_cond1_ts1755007845834, complex_cond2_ts1755007845834;
                                // BEGIN: case_basic_ts1755007845840
                                always_comb begin
                                    inj_out_res_1755007845840_196 = 1'b0;
                                    case (inj_large_data_in_1755007845811_216)
                                        2'b00: inj_out_res_1755007845840_196 = 1'b0;
                                        2'b01: inj_out_res_1755007845840_196 = 1'b1;
                                        2'b10: inj_out_res_1755007845840_196 = 1'b0;
                                        2'b11: inj_out_res_1755007845840_196 = 1'b1;
                                    endcase
                                end
                                // END: case_basic_ts1755007845840

                            assign cond1_ts1755007845834 = part_var_ts1755007845808[0] && part_var_ts1755007845808[1];
                            assign cond2_ts1755007845834 = part_var_ts1755007845808[2] || part_var_ts1755007845808[3];
                            assign cond3_ts1755007845834 = !part_var_ts1755007845808[0];
                            assign complex_cond1_ts1755007845834 = (cond1_ts1755007845834 || cond2_ts1755007845834) && cond3_ts1755007845834;
                            assign complex_cond2_ts1755007845834 = !(part_var_ts1755007845808[0] && part_var_ts1755007845808[1]) || (part_var_ts1755007845808[2] || !part_var_ts1755007845808[3]);
                            always_comb begin
                                inj_out1_1755007845833_320 = '0;
                                if (complex_cond1_ts1755007845834) begin
                                    inj_out1_1755007845833_320 = reg_var_ts1755007845808 + temp_val_e_ts1755007845813;
                                end else begin
                                    inj_out1_1755007845833_320 = reg_var_ts1755007845808 ^ current_large_sum_ts1755007845811;
                                end
                                if (complex_cond2_ts1755007845834) begin
                                    inj_out1_1755007845833_320 = inj_out1_1755007845833_320 + current_large_sum_ts1755007845811;
                                end else begin
                                    inj_out1_1755007845833_320 = inj_out1_1755007845833_320 - current_large_sum_ts1755007845811;
                                end
                                if ((part_var_ts1755007845808[0] && part_var_ts1755007845808[1]) && (!part_var_ts1755007845808[2] || part_var_ts1755007845808[3])) begin
                                    inj_out1_1755007845833_320 = inj_out1_1755007845833_320 * 2;
                                end
                            end
                            // END: dup_logic_ops_ts1755007845834

                            // BEGIN: split_vector_assign_ts1755007845828
                            always @(posedge clk) begin
                                if (inj_a_1755007845810_982) begin
                                    inj_out_vec_y_1755007845828_846[3:0] <= reg_var_ts1755007845808[3:0];
                                    inj_out_vec_y_1755007845828_846[7:4] <= reg_var_ts1755007845808[7:4] + 1;
                                end else begin
                                    inj_out_vec_y_1755007845828_846 <= 8'hFF;
                                end
                            end
                            // END: split_vector_assign_ts1755007845828

                            child_concat_output child_concat_output_inst_1755007845824_2206 (
                                .dummy_in(temp_v_ts1755007845810),
                                .data(inj_data_1755007845824_538)
                            );
                            // BEGIN: mod_if_else_simple_ts1755007845820
                        always_comb begin
                            if (inj_in_data_1755007845820_672 > 8) begin
                                inj_out_result_1755007845820_265 = inj_in_data_1755007845820_672 + 1;
                            end else begin
                                inj_out_result_1755007845820_265 = inj_in_data_1755007845820_672 - 1;
                            end
                        end
                            // END: mod_if_else_simple_ts1755007845820

                            // BEGIN: DummyHierModule_ts1755007845819
                            assign inj_out_logic_1755007845819_848 = inj_in_1755007845807_18;
                            // END: DummyHierModule_ts1755007845819

                            // BEGIN: LintCombBlockAssign_ts1755007845817
                            always_comb begin
                                inj_out_e_1755007845817_920 = c_ts1755007845810 & temp_v_ts1755007845810;
                            end
                            // END: LintCombBlockAssign_ts1755007845817

                            // BEGIN: case_unique_casez_reordered_mod_ts1755007845816
                            always @* begin
                                unique casez ({inj_large_data_in_1755007845811_216[0], part_var_ts1755007845808[3:2], inj_large_data_in_1755007845811_216[1]})
                                    4'b1?0?: inj_internal_out_1755007845816_659 = 30;
                                    4'b?101: inj_internal_out_1755007845816_659 = 31;  
                                    4'b0?1?: inj_internal_out_1755007845816_659 = 32;
                                    4'b1?1?: inj_internal_out_1755007845816_659 = 33;  
                                    4'b?111: inj_internal_out_1755007845816_659 = 34;  
                                endcase
                            end
                            // END: case_unique_casez_reordered_mod_ts1755007845816

                            Comb_IfElse Comb_IfElse_inst_1755007845814_1926 (
                                .condition(clk),
                                .value1(inj_value1_1755007845814_81),
                                .value2(inj_value2_1755007845814_16),
                                .result_val(inj_result_val_1755007845814_697)
                            );
                        always @(posedge clk) begin
                            temp_val_e_ts1755007845813 <= reg_var_ts1755007845808 + 5;
                            if (temp_v_ts1755007845810) begin
                                inj_out_val_e_1755007845813_125 <= temp_val_e_ts1755007845813;
                                inj_status_e_1755007845813_134 <= 1;
                            end else begin
                                inj_out_val_e_1755007845813_125 <= temp_ts1755007845808;
                                inj_status_e_1755007845813_134 <= 0;
                            end
                        end
                        // END: split_mixed_cond_seq_ts1755007845813

                        constant_sel constant_sel_inst_1755007845812_9399 (
                            .out2(inj_out2_1755007845812_97),
                            .in(inj_in_1755007845812_742),
                            .out1(inj_out1_1755007845812_241)
                        );
                    always_comb begin
                        current_large_sum_ts1755007845811 = 8'h00;
                        for (int m = 0; m < 40; m = m + 1) begin 
                            current_large_sum_ts1755007845811 = current_large_sum_ts1755007845811 + inj_large_data_in_1755007845811_216[0];
                            current_large_sum_ts1755007845811 = current_large_sum_ts1755007845811 + inj_large_data_in_1755007845811_216[1];
                            current_large_sum_ts1755007845811 = current_large_sum_ts1755007845811 + 1;
                        end
                        inj_large_sum_out_1755007845811_409 = current_large_sum_ts1755007845811;
                    end
                    // END: loop_unroll_limit_test_ts1755007845811

                    FunctionTaskMod FunctionTaskMod_inst_1755007845810_6154 (
                        .is_even(inj_is_even_1755007845810_881),
                        .data_in(temp_ts1755007845808)
                    );
                temp_v_ts1755007845810 = d_ts1755007845810;
                c_ts1755007845810      = temp_v_ts1755007845810;
            end
            assign inj_out_a_1755007845810_880 = inj_a_1755007845810_982;
            assign d_ts1755007845810     = inj_in_val_1755007845809_372;
            assign inj_out_b_1755007845810_828 = d_ts1755007845810 + P1 + LP1;
            // END: ModuleBasic_ts1755007845810

            // BEGIN: module_in_program_ref_ts1755007845809
            assign inj_out_val_1755007845809_97 = inj_in_val_1755007845809_372;
            // END: module_in_program_ref_ts1755007845809

            // BEGIN: split_single_stmt_ts1755007845809
            always @(*) begin
                inj_out_q_1755007845809_794 = inj_in_val_1755007845808_930 + 1;
            end
            // END: split_single_stmt_ts1755007845809

        always_comb begin
            temp_ts1755007845808 = inj_in_val_1755007845808_930 + reg_var_ts1755007845808;
        end
        assign inj_out_ops_1755007845808_521 = (inj_in_val_1755007845808_930 & reg_var_ts1755007845808) | (inj_in_val_1755007845808_930 ^ reg_var_ts1755007845808);
        assign inj_out_cmp_1755007845808_428 = (inj_in_val_1755007845808_930 == reg_var_ts1755007845808);
        // END: Module_BasicSyntax_ts1755007845808

    always_comb begin
        reg_var_ts1755007845808  = inj_in_val_1755007845808_930;
        part_var_ts1755007845808 = 4'h0;
        for (int i = 0; i < 4; i++) begin
            reg_var_ts1755007845808  = reg_var_ts1755007845808 + i;
            reg_var_ts1755007845808 += (i * 2);
            reg_var_ts1755007845808 <<= inj_in_val_1755007845807_91;
            reg_var_ts1755007845808[i % 8] = (reg_var_ts1755007845808[i % 8] == 1'b0);
            reg_var_ts1755007845808[PART_START +: PART_WIDTH] = i[3:0];
        end
        part_var_ts1755007845808 = reg_var_ts1755007845808[7:4];
    end
    assign inj_out_reg_1755007845808_639  = reg_var_ts1755007845808;
    assign inj_out_part_1755007845808_467 = part_var_ts1755007845808;
    // END: module_assignments_in_loops_ts1755007845808

    assign inj_dummy_out_1755007845807_220 = inj_in_1755007845807_18;
    // END: module_finish_numbers_ts1755007845807

    assign inj_out_1755007845807_850 = inj_in_1755007845807_18;
    // END: BindSimpleModule_ts1755007845807

    always_comb begin
        inj_out_res_1755007845807_886 = 1'b0;
        casez (inj_in_val_1755007845807_91)
            3'b1?z: inj_out_res_1755007845807_886 = 1'b1;
            3'b0z?: inj_out_res_1755007845807_886 = 1'b0;
            default: inj_out_res_1755007845807_886 = 1'b1;
        endcase
    end
    // END: casez_xz_alt_ts1755007845807
endmodule

