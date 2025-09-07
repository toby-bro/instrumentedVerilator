module DummyHierModule (
    input bit in_bit,
    output logic out_logic
);
    assign out_logic = in_bit;
endmodule

module child_concat_output (
    input logic dummy_in,
    output logic [7:0] data
);
    assign data = dummy_in ? 8'hAA : 8'h55;
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

module mod_name_conflict (
    input logic in_a,
    output logic out_a
);
    logic conflict_var;
    parameter int conflict_param = 1;
    assign out_a = in_a;
endmodule

module split_arith_nb (
    input logic clk_v,
    input logic [7:0] op1_v,
    input logic [7:0] op2_v,
    output logic [7:0] diff_v,
    output logic [7:0] prod_v,
    output logic [7:0] sum_v
);
    always @(posedge clk_v) begin
        sum_v <= op1_v + op2_v;
        diff_v <= op1_v - op2_v;
        prod_v <= op1_v * op2_v;
    end
endmodule

module snippet (
    input wire clk,
    input logic [15:0] inj_dividend_mod_1755007760149_62,
    input logic inj_fs_in_target_1755007760149_161,
    input wire inj_g_in_1755007760153_600,
    input wire [7:0] inj_in1_1755007760150_23,
    input logic inj_in2_1755007760150_270,
    input wire [7:0] inj_in2_1755007760150_360,
    input logic [7:0] inj_in_a_j_1755007760149_550,
    input logic [7:0] inj_in_b_j_1755007760149_852,
    input bit inj_in_bit_1755007760149_37,
    input bit [3:0] inj_in_mask_z_1755007760151_908,
    input logic [1:0] inj_in_val_1755007760149_108,
    input logic [15:0] inj_numerator_1755007760149_735,
    input wire reset,
    output logic [7:0] inj_data_1755007760152_654,
    output logic [7:0] inj_diff_v_1755007760149_397,
    output logic inj_dummy_1755007760150_531,
    output logic inj_fs_out_target_1755007760149_301,
    output logic inj_fs_out_target_1755007760152_719,
    output wire inj_g_out_and_1755007760153_75,
    output wire inj_g_out_or_1755007760153_517,
    output logic [7:0] inj_o1_s_1755007760154_685,
    output logic [7:0] inj_o2_s_1755007760154_551,
    output logic [7:0] inj_o3_s_1755007760154_409,
    output logic inj_o_sum_1755007760153_687,
    output wire [7:0] inj_out1_1755007760150_774,
    output wire [7:0] inj_out2_1755007760150_668,
    output logic inj_out_1755007760150_355,
    output logic inj_out_a_1755007760151_932,
    output logic inj_out_logic_1755007760149_158,
    output bit [1:0] inj_out_match_type_z_1755007760151_253,
    output reg inj_out_res_1755007760149_203,
    output logic [7:0] inj_out_x_j_1755007760149_185,
    output logic [7:0] inj_out_y_j_1755007760149_493,
    output logic [7:0] inj_prod_v_1755007760149_388,
    output logic [15:0] inj_quotient_1755007760149_604,
    output logic [7:0] inj_remainder_1755007760149_338,
    output logic [7:0] inj_sum_v_1755007760149_153,
    output logic [7:0] inj_wide_reg_1755007760153_853
);
    // BEGIN: mod_fixup_target_ts1755007760149
    // BEGIN: split_multiple_in_branch_ts1755007760149
    // BEGIN: div_mod_ops_ts1755007760149
    // BEGIN: case_single_default_after_item_ts1755007760149
    // BEGIN: mod_err_event_constant_ts1755007760150
    // BEGIN: simple_xor_gate_ts1755007760150
    // BEGIN: multi_always_comb_ts1755007760150
    logic [7:0] intermediate1_ts1755007760150;
    logic [7:0] intermediate2_ts1755007760150;
        // BEGIN: mod_lint_target_ts1755007760153
        logic l_reg_ts1755007760153;
            // BEGIN: split_complex_nb_ts1755007760154
            logic [7:0] t1_s_ts1755007760154, t2_s_ts1755007760154;
            always @(posedge clk) begin
                t1_s_ts1755007760154 <= inj_in_b_j_1755007760149_852 + intermediate2_ts1755007760150;
                inj_o1_s_1755007760154_685 <= t1_s_ts1755007760154 - intermediate1_ts1755007760150;
                t2_s_ts1755007760154 <= intermediate2_ts1755007760150 * intermediate1_ts1755007760150;
                inj_o2_s_1755007760154_551 <= t1_s_ts1755007760154 + t2_s_ts1755007760154;
                inj_o3_s_1755007760154_409 <= t2_s_ts1755007760154 / 2;
            end
            // END: split_complex_nb_ts1755007760154

            // BEGIN: Module_GatePrimitives_ts1755007760153
            and a1 (inj_g_out_and_1755007760153_75, inj_g_in_1755007760153_600, inj_g_in_1755007760153_600);
            or  o1 (inj_g_out_or_1755007760153_517 , inj_g_in_1755007760153_600, inj_g_in_1755007760153_600);
            // END: Module_GatePrimitives_ts1755007760153

        always_comb begin
            l_reg_ts1755007760153 = 1;
            inj_wide_reg_1755007760153_853 = {reset, clk};
        end
        assign inj_o_sum_1755007760153_687 = reset + clk;
        // END: mod_lint_target_ts1755007760153

        child_concat_output child_concat_output_inst_1755007760152_7792 (
            .data(inj_data_1755007760152_654),
            .dummy_in(inj_in2_1755007760150_270)
        );
        // BEGIN: mod_fixup_target_ts1755007760152
        assign inj_fs_out_target_1755007760152_719 = inj_fs_in_target_1755007760149_161;
        // END: mod_fixup_target_ts1755007760152

        mod_name_conflict mod_name_conflict_inst_1755007760151_7406 (
            .in_a(inj_in2_1755007760150_270),
            .out_a(inj_out_a_1755007760151_932)
        );
        mod_casez_wildcard mod_casez_wildcard_inst_1755007760151_2531 (
            .out_match_type_z(inj_out_match_type_z_1755007760151_253),
            .in_mask_z(inj_in_mask_z_1755007760151_908)
        );
    always @(*) begin
        intermediate1_ts1755007760150 = inj_in1_1755007760150_23 & inj_in2_1755007760150_360;
    end
    always @(*) begin
        intermediate2_ts1755007760150 = inj_in1_1755007760150_23 | inj_in2_1755007760150_360;
    end
    assign inj_out1_1755007760150_774 = intermediate1_ts1755007760150 + 8'd1;
    assign inj_out2_1755007760150_668 = intermediate2_ts1755007760150 - 8'd1;
    // END: multi_always_comb_ts1755007760150

    assign inj_out_1755007760150_355 = inj_fs_in_target_1755007760149_161 ^ inj_in2_1755007760150_270;
    // END: simple_xor_gate_ts1755007760150

    always @(posedge 1'b1) begin
        inj_dummy_1755007760150_531 = ~inj_dummy_1755007760150_531;
    end
    // END: mod_err_event_constant_ts1755007760150

    always_comb begin
        inj_out_res_1755007760149_203 = 1'b0;
        case (inj_in_val_1755007760149_108)
            2'b01: inj_out_res_1755007760149_203 = 1'b1;
            default: inj_out_res_1755007760149_203 = 1'b0;
            2'b10: inj_out_res_1755007760149_203 = 1'b1;
        endcase
    end
    // END: case_single_default_after_item_ts1755007760149

    split_arith_nb split_arith_nb_inst_1755007760149_5882 (
        .op2_v(inj_in_a_j_1755007760149_550),
        .diff_v(inj_diff_v_1755007760149_397),
        .prod_v(inj_prod_v_1755007760149_388),
        .sum_v(inj_sum_v_1755007760149_153),
        .clk_v(clk),
        .op1_v(inj_in_b_j_1755007760149_852)
    );
    assign inj_quotient_1755007760149_604 = (inj_in_b_j_1755007760149_852 == 0) ? 16'hFFFF : (inj_numerator_1755007760149_735 / inj_in_b_j_1755007760149_852); 
    assign inj_remainder_1755007760149_338 = (inj_in_a_j_1755007760149_550 == 0) ? 8'hFF : (inj_dividend_mod_1755007760149_62 % inj_in_a_j_1755007760149_550);
    // END: div_mod_ops_ts1755007760149

    DummyHierModule DummyHierModule_inst_1755007760149_916 (
        .out_logic(inj_out_logic_1755007760149_158),
        .in_bit(inj_in_bit_1755007760149_37)
    );
    always @(posedge clk) begin
        if (inj_fs_in_target_1755007760149_161) begin
            inj_out_x_j_1755007760149_185 <= inj_in_a_j_1755007760149_550 * 3;
            inj_out_y_j_1755007760149_493 <= inj_in_b_j_1755007760149_852 + 1;
        end else begin
            inj_out_x_j_1755007760149_185 <= inj_in_a_j_1755007760149_550;
            inj_out_y_j_1755007760149_493 <= inj_in_b_j_1755007760149_852;
        end
    end
    // END: split_multiple_in_branch_ts1755007760149

    assign inj_fs_out_target_1755007760149_301 = inj_fs_in_target_1755007760149_161;
    // END: mod_fixup_target_ts1755007760149
endmodule

