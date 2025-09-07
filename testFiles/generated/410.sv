module LintImplicitWidth (
    input logic [7:0] in_wide,
    output logic [3:0] out_narrow
);
    assign out_narrow = in_wide;
endmodule

module split_combo_blocking (
    input logic [7:0] a_aa,
    input logic [7:0] b_aa,
    input logic [7:0] c_aa,
    output logic [7:0] x_aa,
    output logic [7:0] y_aa,
    output logic [7:0] z_aa
);
    always @(*) begin
        x_aa = a_aa + b_aa;
        y_aa = x_aa - c_aa;
        z_aa = a_aa * c_aa;
    end
endmodule

module typedef_union_mod (
    input logic [15:0] packed_in,
    output logic [7:0] field0_byte_o
);
    typedef union packed {
        logic [15:0] word;
        logic [1:0][7:0] byte_fields;
    } my_packed_union_t;
    my_packed_union_t my_union_var;
    always_comb begin
        my_union_var.word = packed_in;
    end
    assign field0_byte_o = my_union_var.byte_fields[0];
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_b_aa_1755007891389_519,
    input logic [7:0] inj_c_aa_1755007891389_983,
    input logic inj_condition_t_1755007891387_692,
    input logic [7:0] inj_in_val_t_1755007891387_671,
    input logic [31:0] inj_in_vec_1755007891388_206,
    input logic [15:0] inj_packed_in_1755007891392_761,
    input logic [1:0] inj_sel_1755007891393_755,
    input int inj_start_index_1755007891388_923,
    input wire [31:0] inj_wide_in_1755007891395_172,
    input int inj_width_1755007891388_810,
    input wire reset,
    output logic inj_cond_out_1755007891390_698,
    output logic [7:0] inj_field0_byte_o_1755007891392_858,
    output wire [7:0] inj_lower_byte_out_1755007891395_357,
    output logic inj_o_sum_1755007891396_832,
    output logic [7:0] inj_out_case_a_1755007891393_439,
    output logic [7:0] inj_out_case_b_1755007891393_558,
    output logic [7:0] inj_out_down_1755007891388_482,
    output logic [3:0] inj_out_narrow_1755007891391_823,
    output logic [7:0] inj_out_reg_t_1755007891387_946,
    output logic [7:0] inj_out_up_1755007891388_128,
    output wire [7:0] inj_upper_byte_out_1755007891395_301,
    output logic [7:0] inj_wide_reg_1755007891396_871,
    output logic [7:0] inj_x_aa_1755007891389_860,
    output logic [7:0] inj_y_aa_1755007891389_30,
    output logic [7:0] inj_z_aa_1755007891389_577
);
    // BEGIN: split_if_empty_branches_ts1755007891387
    // BEGIN: range_select_indexed_packed_ts1755007891388
    // BEGIN: mod_logical_not_ts1755007891390
    // BEGIN: mod_split_case_ts1755007891393
    logic [7:0]  split_case_var_ts1755007891393;
    logic [7:0] other_case_var_ts1755007891393;
        // BEGIN: part_select_ops_ts1755007891395
        wire [31:0] processed_wide_ts1755007891395;
            // BEGIN: mod_lint_target_ts1755007891397
            logic l_reg_ts1755007891397;
            always_comb begin
                l_reg_ts1755007891397 = 1;
                inj_wide_reg_1755007891396_871 = {reset, clk};
            end
            assign inj_o_sum_1755007891396_832 = reset + clk;
            // END: mod_lint_target_ts1755007891397

        assign processed_wide_ts1755007891395 = inj_wide_in_1755007891395_172 * 2;
        assign inj_upper_byte_out_1755007891395_301 = processed_wide_ts1755007891395[31:24];
        assign inj_lower_byte_out_1755007891395_357 = processed_wide_ts1755007891395[7:0];
        // END: part_select_ops_ts1755007891395

    always_comb begin
        split_case_var_ts1755007891393 = 8'hFF;
        other_case_var_ts1755007891393 = 8'hAA;
        case (inj_sel_1755007891393_755)
            2'b00: begin
                split_case_var_ts1755007891393 = inj_c_aa_1755007891389_983 + 5;
                other_case_var_ts1755007891393 = inj_c_aa_1755007891389_983 + 6;
            end
            2'b01: begin
                split_case_var_ts1755007891393 = inj_c_aa_1755007891389_983 - 5;
                other_case_var_ts1755007891393 = inj_c_aa_1755007891389_983 - 6;
            end
            default: begin
                split_case_var_ts1755007891393 = inj_c_aa_1755007891389_983;
                other_case_var_ts1755007891393 = inj_c_aa_1755007891389_983;
            end
        endcase
        inj_out_case_a_1755007891393_439 = split_case_var_ts1755007891393;
        inj_out_case_b_1755007891393_558 = other_case_var_ts1755007891393;
    end
    // END: mod_split_case_ts1755007891393

    typedef_union_mod typedef_union_mod_inst_1755007891392_6905 (
        .field0_byte_o(inj_field0_byte_o_1755007891392_858),
        .packed_in(inj_packed_in_1755007891392_761)
    );
    LintImplicitWidth LintImplicitWidth_inst_1755007891391_5159 (
        .out_narrow(inj_out_narrow_1755007891391_823),
        .in_wide(inj_b_aa_1755007891389_519)
    );
    always_comb begin
        inj_cond_out_1755007891390_698 = !inj_condition_t_1755007891387_692;
    end
    // END: mod_logical_not_ts1755007891390

    split_combo_blocking split_combo_blocking_inst_1755007891389_8613 (
        .b_aa(inj_b_aa_1755007891389_519),
        .c_aa(inj_c_aa_1755007891389_983),
        .x_aa(inj_x_aa_1755007891389_860),
        .y_aa(inj_y_aa_1755007891389_30),
        .z_aa(inj_z_aa_1755007891389_577),
        .a_aa(inj_in_val_t_1755007891387_671)
    );
    always_comb begin
        if (inj_start_index_1755007891388_923 >= 0 && inj_width_1755007891388_810 > 0 && inj_start_index_1755007891388_923 + inj_width_1755007891388_810 <= 32) begin
            case (inj_width_1755007891388_810)
                1: inj_out_up_1755007891388_128 = inj_in_vec_1755007891388_206[inj_start_index_1755007891388_923 +: 1];
                2: inj_out_up_1755007891388_128 = inj_in_vec_1755007891388_206[inj_start_index_1755007891388_923 +: 2];
                4: inj_out_up_1755007891388_128 = inj_in_vec_1755007891388_206[inj_start_index_1755007891388_923 +: 4];
                8: inj_out_up_1755007891388_128 = inj_in_vec_1755007891388_206[inj_start_index_1755007891388_923 +: 8];
                default: inj_out_up_1755007891388_128 = 'x;
            endcase
        end else begin
            inj_out_up_1755007891388_128 = 'x;
        end
        if (inj_start_index_1755007891388_923 >= inj_width_1755007891388_810 - 1 && inj_width_1755007891388_810 > 0 && inj_start_index_1755007891388_923 < 32) begin
            case (inj_width_1755007891388_810)
                1: inj_out_down_1755007891388_482 = inj_in_vec_1755007891388_206[inj_start_index_1755007891388_923 -: 1];
                2: inj_out_down_1755007891388_482 = inj_in_vec_1755007891388_206[inj_start_index_1755007891388_923 -: 2];
                4: inj_out_down_1755007891388_482 = inj_in_vec_1755007891388_206[inj_start_index_1755007891388_923 -: 4];
                8: inj_out_down_1755007891388_482 = inj_in_vec_1755007891388_206[inj_start_index_1755007891388_923 -: 8];
                default: inj_out_down_1755007891388_482 = 'x;
            endcase
        end else begin
            inj_out_down_1755007891388_482 = 'x;
        end
    end
    // END: range_select_indexed_packed_ts1755007891388

    always @(posedge clk) begin
        if (inj_condition_t_1755007891387_692) begin
        end else begin
        end
    end
    // END: split_if_empty_branches_ts1755007891387
endmodule

