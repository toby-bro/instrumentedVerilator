module snippet (
    input wire clk,
    input logic [7:0] inj_a_aa_1755007788734_611,
    input logic [7:0] inj_b_aa_1755007788734_709,
    input logic [7:0] inj_data_in_1755007788732_354,
    input logic inj_i_data_1755007788732_780,
    input integer inj_in_int_1755007788733_296,
    input logic [31:0] inj_in_l32_1755007788733_442,
    input wire [15:0] inj_in_packed_data_1755007788732_918,
    input logic [15:0] inj_in_u16_1755007788733_878,
    input wire reset,
    output logic inj_dummy_out_1755007788732_510,
    output logic inj_dummy_out_1755007788736_896,
    output logic inj_o_result_1755007788732_863,
    output wire [7:0] inj_out_byte_1755007788732_902,
    output logic signed [15:0] inj_out_s16_1755007788733_189,
    output logic signed [31:0] inj_out_s32_from_int_1755007788733_106,
    output logic signed [31:0] inj_out_s32_from_l32_1755007788733_791,
    output logic [31:0] inj_out_u32_from_int_1755007788733_31,
    output logic [31:0] inj_out_u32_from_l32_1755007788733_571,
    output logic [7:0] inj_out_u8_1755007788733_808,
    output logic [7:0] inj_out_x_j_1755007788735_715,
    output logic [7:0] inj_out_y_j_1755007788735_774,
    output bit inj_system_status_clear_1755007788736_729,
    output logic [7:0] inj_x_aa_1755007788734_251,
    output logic [7:0] inj_y_aa_1755007788734_445,
    output logic [7:0] inj_z_aa_1755007788734_777
);
    // BEGIN: packed_struct_module_ts1755007788732
    typedef struct packed {
        logic [7:0] byte1_ts1755007788732;
        logic [7:0] byte2_ts1755007788732;
    } my_packed_struct_t;
    my_packed_struct_t data_struct;
    // BEGIN: mod_simple_ref_ts1755007788732
    logic internal_sig_ts1755007788732;
    // BEGIN: mixed_conn_child_ts1755007788733
    logic dummy_internal_ts1755007788733;
    // BEGIN: mixed_conn_child_ts1755007788736
    logic dummy_internal_ts1755007788736;
    // BEGIN: PragmaResetDirectives_ts1755007788736
`ifdef SLANG_PRAGMA
`reset protect diagnostic
`endif
assign inj_system_status_clear_1755007788736_729 = reset;
    // END: PragmaResetDirectives_ts1755007788736

    always_comb dummy_internal_ts1755007788736 = |inj_b_aa_1755007788734_709 | inj_i_data_1755007788732_780;
    assign inj_dummy_out_1755007788736_896 = dummy_internal_ts1755007788736;
    // END: mixed_conn_child_ts1755007788736

    // BEGIN: split_multiple_in_branch_ts1755007788735
    always @(posedge clk) begin
        if (inj_i_data_1755007788732_780) begin
            inj_out_x_j_1755007788735_715 <= inj_data_in_1755007788732_354 * 3;
            inj_out_y_j_1755007788735_774 <= inj_a_aa_1755007788734_611 + 1;
        end else begin
            inj_out_x_j_1755007788735_715 <= inj_data_in_1755007788732_354;
            inj_out_y_j_1755007788735_774 <= inj_a_aa_1755007788734_611;
        end
    end
    // END: split_multiple_in_branch_ts1755007788735

    // BEGIN: split_combo_blocking_ts1755007788734
    always @(*) begin
        inj_x_aa_1755007788734_251 = inj_a_aa_1755007788734_611 + inj_b_aa_1755007788734_709;
        inj_y_aa_1755007788734_445 = inj_x_aa_1755007788734_251 - inj_data_in_1755007788732_354;
        inj_z_aa_1755007788734_777 = inj_a_aa_1755007788734_611 * inj_data_in_1755007788732_354;
    end
    // END: split_combo_blocking_ts1755007788734

    // BEGIN: SignedUnsignedConversions_ts1755007788733
    always_comb begin
        inj_out_u8_1755007788733_808 = $unsigned(inj_data_in_1755007788732_354);
        inj_out_s16_1755007788733_189 = $signed(inj_in_u16_1755007788733_878);
        inj_out_s32_from_l32_1755007788733_791 = $signed(inj_in_l32_1755007788733_442);
        inj_out_u32_from_l32_1755007788733_571 = $unsigned(inj_in_l32_1755007788733_442);
        inj_out_s32_from_int_1755007788733_106 = $signed(inj_in_int_1755007788733_296);
        inj_out_u32_from_int_1755007788733_31 = $unsigned(inj_in_int_1755007788733_296);
    end
    // END: SignedUnsignedConversions_ts1755007788733

    always_comb dummy_internal_ts1755007788733 = |inj_data_in_1755007788732_354 | inj_i_data_1755007788732_780;
    assign inj_dummy_out_1755007788732_510 = dummy_internal_ts1755007788733;
    // END: mixed_conn_child_ts1755007788733

    always_comb begin
        internal_sig_ts1755007788732 = inj_i_data_1755007788732_780;
        inj_o_result_1755007788732_863 = internal_sig_ts1755007788732;
    end
    // END: mod_simple_ref_ts1755007788732

    assign data_struct = inj_in_packed_data_1755007788732_918;
    assign inj_out_byte_1755007788732_902 = data_struct.byte1_ts1755007788732;
    // END: packed_struct_module_ts1755007788732
endmodule

