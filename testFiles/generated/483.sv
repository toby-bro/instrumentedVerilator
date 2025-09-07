module LintParamUnused #(
    parameter integer UNUSED_PARAM = 8
) (
    input logic in_m,
    output logic out_n
);
    assign out_n = in_m;
endmodule

module ansi_basic (
    input logic clk,
    output logic reset_n
);
    always_comb begin
        reset_n = clk;
    end
endmodule

module case_empty_statement (
    input logic [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b00: out_res = 1'b1;
            2'b01: ;
            2'b10: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
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

module multi_port_decl_module (
    input logic [3:0] p_a,
    input logic [3:0] p_b,
    input logic single_in,
    output logic single_out
);
    always_comb begin
        single_out = single_in;
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

module simple_logic_b (
    input wire data_c,
    output wire data_d
);
    assign data_d = data_c;
endmodule

module split_complex_blocking (
    input logic [7:0] i1_r,
    input logic [7:0] i2_r,
    input logic [7:0] i3_r,
    output logic [7:0] o1_r,
    output logic [7:0] o2_r,
    output logic [7:0] o3_r
);
    logic [7:0] t1_r, t2_r;
    always @(*) begin
        t1_r = i1_r + i2_r;
        o1_r = t1_r - i3_r;
        t2_r = i2_r * i3_r;
        o2_r = t1_r + t2_r;
        o3_r = t2_r / 2;
    end
endmodule

module split_single_stmt (
    input logic [7:0] in_q,
    output logic [7:0] out_q
);
    always @(*) begin
        out_q = in_q + 1;
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_b_1755007915595_396,
    input wire [1:0] inj_byte_idx_1755007915569_959,
    input logic [7:0] inj_c_1755007915595_26,
    input logic [1:0] inj_case_expr_1755007915564_305,
    input logic [3:0] inj_case_inside_val_1755007915564_369,
    input wire [7:0] inj_d_in_1755007915565_821,
    input logic inj_i_gate_1755007915566_148,
    input logic inj_i_in_1755007915566_278,
    input int inj_i_val_1755007915580_266,
    input logic [15:0] inj_in_1755007915564_862,
    input bit [7:0] inj_in_cmd_1755007915585_324,
    input logic [7:0] inj_in_q_1755007915571_890,
    input logic [2:0] inj_mode_1755007915602_342,
    input logic [3:0] inj_p_b_1755007915573_524,
    input wire [31:0] inj_wide_data_1755007915569_262,
    input wire reset,
    output logic inj_anded_1755007915595_695,
    output wire inj_data_d_1755007915564_807,
    output logic inj_diff_1755007915595_989,
    output logic [4:0] inj_internal_out_1755007915564_520,
    output logic [4:0] inj_internal_out_1755007915583_493,
    output logic [7:0] inj_o1_r_1755007915599_458,
    output logic [7:0] inj_o2_r_1755007915599_574,
    output logic [7:0] inj_o3_r_1755007915599_714,
    output logic inj_o_out_1755007915566_989,
    output logic inj_o_out_1755007915570_853,
    output logic inj_o_out_1755007915575_346,
    output logic inj_o_out_1755007915578_30,
    output logic inj_o_out_1755007915606_585,
    output int inj_o_val_1755007915580_618,
    output logic inj_ored_1755007915595_987,
    output logic [15:0] inj_out_1755007915564_385,
    output logic inj_out_1755007915567_450,
    output logic inj_out_md_1755007915567_487,
    output logic inj_out_n_1755007915591_340,
    output logic [7:0] inj_out_q_1755007915571_962,
    output reg inj_out_res_1755007915588_490,
    output bit [3:0] inj_out_status_1755007915585_327,
    output logic inj_out_sub_1755007915564_791,
    output reg [7:0] inj_q_out_1755007915565_876,
    output logic [7:0] inj_res_1755007915602_551,
    output logic inj_reset_n_1755007915577_971,
    output reg [7:0] inj_selected_byte_1755007915569_907,
    output logic inj_single_out_1755007915573_438,
    output logic [7:0] inj_sum_1755007915595_732,
    output logic inj_xored_1755007915595_110,
    output logic [3:0] inj_y_1755007915568_838
);
    // BEGIN: always_comb_assign_ts1755007915564
    // BEGIN: mod_sub_ts1755007915564
    // BEGIN: case_priority_casex_complex_mod_ts1755007915565
    // BEGIN: Seq_DFF_ts1755007915565
    // BEGIN: named_block_logic_ts1755007915566
    logic r_internal_ts1755007915566;
    logic r_temp_ts1755007915566;
        // BEGIN: attributes_on_expr_port_ts1755007915570
        logic internal_sig_ts1755007915570;
            // BEGIN: attributes_on_expr_port_ts1755007915575
            logic internal_sig_ts1755007915575;
                // BEGIN: name_conflict_example_ts1755007915578
                parameter int my_param = 5;
                logic my_var_ts1755007915578;
                    // BEGIN: mod_automatic_task_ts1755007915580
                    task automatic update_val(input int in_v, output int out_v);
                        out_v = in_v * 2;
                    endtask
                    always_comb begin
                        int temp_val_ts1755007915580;
                            attributes_on_expr_port attributes_on_expr_port_inst_1755007915606_2185 (
                                .i_control(internal_sig_ts1755007915575),
                                .i_in(r_internal_ts1755007915566),
                                .o_out(inj_o_out_1755007915606_585)
                            );
                            // BEGIN: dup_nested_if_ts1755007915603
                            always_comb begin
                                inj_res_1755007915602_551 = '0;
                                if (inj_mode_1755007915602_342 == 3'b001) begin
                                    if (inj_b_1755007915595_396 > inj_in_q_1755007915571_890) begin
                                        inj_res_1755007915602_551 = inj_b_1755007915595_396 + inj_in_q_1755007915571_890;
                                    end else begin
                                        inj_res_1755007915602_551 = inj_b_1755007915595_396 - inj_in_q_1755007915571_890;
                                    end
                                end else if (inj_mode_1755007915602_342 == 3'b010) begin
                                    if (inj_b_1755007915595_396 > inj_in_q_1755007915571_890) begin
                                        inj_res_1755007915602_551 = inj_b_1755007915595_396 + inj_in_q_1755007915571_890;
                                    end else begin
                                        inj_res_1755007915602_551 = inj_b_1755007915595_396 - inj_in_q_1755007915571_890;
                                    end
                                end else if (inj_mode_1755007915602_342 == 3'b011) begin
                                    if (inj_b_1755007915595_396 < inj_in_q_1755007915571_890) begin
                                        inj_res_1755007915602_551 = inj_b_1755007915595_396 * inj_in_q_1755007915571_890;
                                    end else begin
                                        inj_res_1755007915602_551 = inj_b_1755007915595_396 / ((inj_in_q_1755007915571_890 == 0) ? 1 : inj_in_q_1755007915571_890);
                                    end
                                end else if (inj_mode_1755007915602_342 == 3'b100) begin
                                    if (inj_b_1755007915595_396 != inj_in_q_1755007915571_890) begin
                                        if (inj_b_1755007915595_396 > inj_in_q_1755007915571_890) inj_res_1755007915602_551 = inj_b_1755007915595_396;
                                        else inj_res_1755007915602_551 = inj_in_q_1755007915571_890;
                                    end else begin
                                        inj_res_1755007915602_551 = inj_b_1755007915595_396 + inj_in_q_1755007915571_890;
                                    end
                                end
                                else begin
                                    inj_res_1755007915602_551 = inj_b_1755007915595_396 ^ inj_in_q_1755007915571_890;
                                end
                            end
                            // END: dup_nested_if_ts1755007915603

                            split_complex_blocking split_complex_blocking_inst_1755007915599_5656 (
                                .o2_r(inj_o2_r_1755007915599_574),
                                .o3_r(inj_o3_r_1755007915599_714),
                                .i1_r(inj_c_1755007915595_26),
                                .i2_r(inj_b_1755007915595_396),
                                .i3_r(inj_in_q_1755007915571_890),
                                .o1_r(inj_o1_r_1755007915599_458)
                            );
                            // BEGIN: more_ops_ts1755007915595
                            assign inj_sum_1755007915595_732 = inj_in_q_1755007915571_890 + inj_b_1755007915595_396;
                            assign inj_diff_1755007915595_989 = inj_in_q_1755007915571_890 > inj_c_1755007915595_26;
                            assign inj_anded_1755007915595_695 = inj_in_q_1755007915571_890 & inj_b_1755007915595_396;
                            assign inj_ored_1755007915595_987 = inj_in_q_1755007915571_890 | inj_c_1755007915595_26;
                            assign inj_xored_1755007915595_110 = inj_in_q_1755007915571_890 ^ inj_b_1755007915595_396;
                            // END: more_ops_ts1755007915595

                            LintParamUnused LintParamUnused_inst_1755007915591_6352 (
                                .out_n(inj_out_n_1755007915591_340),
                                .in_m(internal_sig_ts1755007915575)
                            );
                            case_empty_statement case_empty_statement_inst_1755007915588_8746 (
                                .out_res(inj_out_res_1755007915588_490),
                                .in_val(inj_case_expr_1755007915564_305)
                            );
                            // BEGIN: mod_case_standard_ts1755007915585
                        always_comb begin
                            case (inj_in_cmd_1755007915585_324)
                                8'd0, 8'd1, 8'd2: begin
                                    inj_out_status_1755007915585_327 = 4'hA;
                                end
                                8'd3, 8'd4: begin
                                    inj_out_status_1755007915585_327 = 4'hB;
                                end
                                default: begin
                                    inj_out_status_1755007915585_327 = 4'hF;
                                end
                            endcase
                        end
                            // END: mod_case_standard_ts1755007915585

                            case_unique0_violating_mod case_unique0_violating_mod_inst_1755007915583_4273 (
                                .case_expr(inj_case_expr_1755007915564_305),
                                .internal_out(inj_internal_out_1755007915583_493)
                            );
                        update_val(inj_i_val_1755007915580_266, temp_val_ts1755007915580);
                        inj_o_val_1755007915580_618 = temp_val_ts1755007915580;
                    end
                    // END: mod_automatic_task_ts1755007915580

                always_comb my_var_ts1755007915578 = internal_sig_ts1755007915575;
                assign inj_o_out_1755007915578_30 = internal_sig_ts1755007915575 && (my_param == 5) && my_var_ts1755007915578;
                // END: name_conflict_example_ts1755007915578

                ansi_basic ansi_basic_inst_1755007915577_8928 (
                    .reset_n(inj_reset_n_1755007915577_971),
                    .clk(clk)
                );
            assign internal_sig_ts1755007915575 = inj_i_in_1755007915566_278 & r_internal_ts1755007915566;
            simple_adder sa_inst(
                .a  (inj_i_in_1755007915566_278),
                (* fanout_limit = 10 *) .b(r_internal_ts1755007915566),
                .sum(inj_o_out_1755007915575_346)
            );
            // END: attributes_on_expr_port_ts1755007915575

            multi_port_decl_module multi_port_decl_module_inst_1755007915573_6864 (
                .p_a(inj_case_inside_val_1755007915564_369),
                .p_b(inj_p_b_1755007915573_524),
                .single_in(internal_sig_ts1755007915570),
                .single_out(inj_single_out_1755007915573_438)
            );
            split_single_stmt split_single_stmt_inst_1755007915571_790 (
                .in_q(inj_in_q_1755007915571_890),
                .out_q(inj_out_q_1755007915571_962)
            );
        assign internal_sig_ts1755007915570 = inj_i_in_1755007915566_278 & r_internal_ts1755007915566;
        simple_adder sa_inst(
            .a  (inj_i_in_1755007915566_278),
            (* fanout_limit = 10 *) .b(r_internal_ts1755007915566),
            .sum(inj_o_out_1755007915570_853)
        );
        // END: attributes_on_expr_port_ts1755007915570

        // BEGIN: Bit_Manip_ts1755007915569
        always_comb begin
            case (inj_byte_idx_1755007915569_959)
                2'b00: inj_selected_byte_1755007915569_907 = inj_wide_data_1755007915569_262[7:0];
                2'b01: inj_selected_byte_1755007915569_907 = inj_wide_data_1755007915569_262[15:8];
                2'b10: inj_selected_byte_1755007915569_907 = inj_wide_data_1755007915569_262[23:16];
                default: inj_selected_byte_1755007915569_907 = inj_wide_data_1755007915569_262[31:24];
            endcase
        end
        // END: Bit_Manip_ts1755007915569

        // BEGIN: AlwaysCombInvert_ts1755007915568
        always_comb inj_y_1755007915568_838 = ~inj_case_inside_val_1755007915564_369;
        // END: AlwaysCombInvert_ts1755007915568

        // BEGIN: ModuleDefinition_ts1755007915567
        assign inj_out_md_1755007915567_487 = clk;
        // END: ModuleDefinition_ts1755007915567

        // BEGIN: simple_and_gate_ts1755007915567
        assign inj_out_1755007915567_450 = inj_i_gate_1755007915566_148 & r_temp_ts1755007915566;
        // END: simple_and_gate_ts1755007915567

    always_comb begin : my_combinational_block
        r_temp_ts1755007915566 = inj_i_in_1755007915566_278 & inj_i_gate_1755007915566_148;
        r_internal_ts1755007915566 = r_temp_ts1755007915566;
        inj_o_out_1755007915566_989 = r_internal_ts1755007915566;
    end
    // END: named_block_logic_ts1755007915566

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            inj_q_out_1755007915565_876 <= 8'b0;
        end else begin
            inj_q_out_1755007915565_876 <= inj_d_in_1755007915565_821;
        end
    end
    // END: Seq_DFF_ts1755007915565

    always @* begin
        priority casex ({inj_case_expr_1755007915564_305, inj_case_inside_val_1755007915564_369[1:0]})
            4'b1???: inj_internal_out_1755007915564_520 = 24;
            4'b?1??: inj_internal_out_1755007915564_520 = 25;  
            4'b??1?: inj_internal_out_1755007915564_520 = 26;  
            4'b???1: inj_internal_out_1755007915564_520 = 27;  
            4'b0000: inj_internal_out_1755007915564_520 = 28;  
            default: inj_internal_out_1755007915564_520 = 29;
        endcase
    end
    // END: case_priority_casex_complex_mod_ts1755007915565

    simple_logic_b simple_logic_b_inst_1755007915564_6465 (
        .data_d(inj_data_d_1755007915564_807),
        .data_c(reset)
    );
    assign inj_out_sub_1755007915564_791 = clk;
    // END: mod_sub_ts1755007915564

    always_comb begin
        inj_out_1755007915564_385 = inj_in_1755007915564_862;
    end
    // END: always_comb_assign_ts1755007915564
endmodule

