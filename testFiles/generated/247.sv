interface simple_if (
    input logic clk
);
    logic data;
    logic ready;
    modport master (output data, input ready);
    modport slave (input data, output ready);
endinterface
module ContinuousWire (
    input logic din,
    output wire dout
);
    wire internal_w;
    assign internal_w = din;
    assign dout       = internal_w;
endmodule

module mod_lint_target (
    input wire i_a,
    input wire i_b,
    output logic o_sum,
    output logic [7:0] wide_reg
);
    logic l_reg;
    always_comb begin
        l_reg = 1;
        wide_reg = {i_a, i_b};
    end
    assign o_sum = i_a + i_b;
endmodule

module module_selection (
    input wire in_bit,
    input wire [2:0] in_index,
    input wire [1:0] in_part_lsb,
    input wire [7:0] in_vector,
    output logic out_bit_select,
    output logic [7:0] out_bitwise_ops,
    output logic [3:0] out_part_select,
    output logic [7:0] out_vector_assign
);
    always_comb begin
    out_vector_assign = in_vector;
    out_bit_select = in_vector[in_index];
    out_part_select = in_vector[in_part_lsb +: 4];
    out_bitwise_ops = in_vector & {8{in_bit}};
    end
endmodule

module part_select_ops (
    input wire [31:0] wide_in,
    output wire [7:0] lower_byte_out,
    output wire [7:0] upper_byte_out
);
    wire [31:0] processed_wide;
    assign processed_wide = wide_in * 2;
    assign upper_byte_out = processed_wide[31:24];
    assign lower_byte_out = processed_wide[7:0];
endmodule

module sub_module (
    input logic sub_in,
    output logic sub_out
);
    assign sub_out = !sub_in;
endmodule

module hierarchy_if (
    input logic clk,
    input logic main_in,
    output logic main_out
);
    sub_module u_sub (
        .sub_in(main_in),
        .sub_out(main_out)
    );
    simple_if if_inst (.clk(clk));
    always_comb begin
        if_inst.data = main_in;
        if_inst.ready = main_out;
    end
endmodule

module super_outside_class_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_a_bb_1755007836816_562,
    input logic [7:0] inj_b_bb_1755007836816_964,
    input logic [7:0] inj_c_bb_1755007836816_660,
    input bit inj_condition_m10_1755007836819_949,
    input wire [2:0] inj_in_index_1755007836817_355,
    input wire [1:0] inj_in_part_lsb_1755007836817_329,
    input int inj_in_val_1755007836814_31,
    input wire [7:0] inj_in_vector_1755007836817_498,
    input logic inj_main_in_1755007836815_478,
    input logic inj_vif_valid_1755007836817_18,
    input wire [31:0] inj_wide_in_1755007836814_310,
    input wire reset,
    output logic inj_data_ref_out_1755007836823_353,
    output wire inj_dout_1755007836818_191,
    output logic inj_dummy_out_1755007836817_893,
    output wire [7:0] inj_lower_byte_out_1755007836814_277,
    output wire [7:0] inj_lower_byte_out_1755007836822_500,
    output logic inj_main_out_1755007836815_777,
    output logic inj_o_sum_1755007836826_548,
    output logic inj_o_sum_1755007836828_922,
    output logic [7:0] inj_out1_1755007836820_203,
    output logic [7:0] inj_out2_1755007836820_157,
    output wire inj_out_1755007836818_378,
    output logic inj_out_bit_select_1755007836817_284,
    output logic [7:0] inj_out_bitwise_ops_1755007836817_399,
    output logic [7:0] inj_out_data_1755007836817_519,
    output logic inj_out_l_1755007836829_645,
    output logic [3:0] inj_out_part_select_1755007836817_443,
    output int inj_out_val_1755007836814_740,
    output logic [7:0] inj_out_val_m10_1755007836819_173,
    output logic inj_out_valid_1755007836817_834,
    output logic [7:0] inj_out_vec_1755007836825_950,
    output logic [7:0] inj_out_vector_assign_1755007836817_156,
    output logic inj_status_out_1755007836823_335,
    output logic inj_sub_out_1755007836821_761,
    output wire [7:0] inj_upper_byte_out_1755007836814_297,
    output wire [7:0] inj_upper_byte_out_1755007836822_670,
    output logic [7:0] inj_wide_reg_1755007836826_337,
    output logic [7:0] inj_wide_reg_1755007836828_157,
    output logic [7:0] inj_x_bb_1755007836816_636,
    output logic [7:0] inj_y_bb_1755007836816_487,
    output logic [7:0] inj_z_bb_1755007836816_54,
    inout wire inj_data_inout_1755007836823_231
);
    // BEGIN: part_select_ops_ts1755007836815
    wire [31:0] processed_wide_ts1755007836814;
        // BEGIN: split_combo_nb_ts1755007836816
        logic [7:0] temp_bb_ts1755007836816;
            // BEGIN: unsupported_cond_expr_ts1755007836819
            logic [7:0] var_m10_ts1755007836819;
                // BEGIN: ModuleComb_ts1755007836820
                logic [7:0] internal_wire_ts1755007836820;
                    // BEGIN: mod_lint_target_ts1755007836826
                    logic l_reg_ts1755007836826;
                        // BEGIN: LintLatch_ts1755007836829
                        always_comb begin
                            if (l_reg_ts1755007836826) begin
                                inj_out_l_1755007836829_645 = inj_main_in_1755007836815_478;
                            end else begin
                                inj_out_l_1755007836829_645 = 1'b0; 
                            end
                        end
                        // END: LintLatch_ts1755007836829

                        mod_lint_target mod_lint_target_inst_1755007836828_7965 (
                            .i_a(clk),
                            .i_b(reset),
                            .o_sum(inj_o_sum_1755007836828_922),
                            .wide_reg(inj_wide_reg_1755007836828_157)
                        );
                    always_comb begin
                        l_reg_ts1755007836826 = 1;
                        inj_wide_reg_1755007836826_337 = {clk, reset};
                    end
                    assign inj_o_sum_1755007836826_548 = clk + reset;
                    // END: mod_lint_target_ts1755007836826

                    // BEGIN: SimpleLoopExample_ts1755007836825
                    always_comb begin
                        for (int i = 0; i < 8; i++) begin
                            inj_out_vec_1755007836825_950[i] = internal_wire_ts1755007836820[7 - i];
                        end
                    end
                    // END: SimpleLoopExample_ts1755007836825

                    // BEGIN: ansi_directions_ts1755007836823
                    logic internal_data = 1'b0;
                    assign inj_data_inout_1755007836823_231 = internal_data;
                    always_comb begin
                        inj_data_ref_out_1755007836823_353 = inj_vif_valid_1755007836817_18;
                        internal_data = inj_data_inout_1755007836823_231;
                        inj_status_out_1755007836823_335 = internal_data | inj_main_in_1755007836815_478;
                    end
                    // END: ansi_directions_ts1755007836823

                    part_select_ops part_select_ops_inst_1755007836822_2173 (
                        .lower_byte_out(inj_lower_byte_out_1755007836822_500),
                        .upper_byte_out(inj_upper_byte_out_1755007836822_670),
                        .wide_in(processed_wide_ts1755007836814)
                    );
                    // BEGIN: sub_module_ts1755007836821
                    assign inj_sub_out_1755007836821_761 = !inj_vif_valid_1755007836817_18;
                    // END: sub_module_ts1755007836821

                assign internal_wire_ts1755007836820 = inj_c_bb_1755007836816_660 + inj_a_bb_1755007836816_562;
                always_comb begin
                    if (internal_wire_ts1755007836820 > 8'd128) begin
                        inj_out1_1755007836820_203 = internal_wire_ts1755007836820 - 1;
                    end else begin
                        inj_out1_1755007836820_203 = internal_wire_ts1755007836820 + 1;
                    end
                    inj_out2_1755007836820_157 = internal_wire_ts1755007836820 / 2;
                end
                // END: ModuleComb_ts1755007836820

            always_comb begin
                var_m10_ts1755007836819 = temp_bb_ts1755007836816;
                inj_out_val_m10_1755007836819_173 = inj_condition_m10_1755007836819_949 ? var_m10_ts1755007836819 : var_m10_ts1755007836819;
                var_m10_ts1755007836819++;
            end
            // END: unsupported_cond_expr_ts1755007836819

            // BEGIN: Comb_Assign_ts1755007836818
            assign inj_out_1755007836818_378 = clk & reset;
            // END: Comb_Assign_ts1755007836818

            ContinuousWire ContinuousWire_inst_1755007836818_9445 (
                .dout(inj_dout_1755007836818_191),
                .din(inj_vif_valid_1755007836817_18)
            );
            // BEGIN: virtual_interface_lookup_mod_ts1755007836817
            always_comb begin
                inj_out_data_1755007836817_519  = temp_bb_ts1755007836816;
                inj_out_valid_1755007836817_834 = inj_vif_valid_1755007836817_18;
                inj_dummy_out_1755007836817_893 = inj_main_in_1755007836815_478;
            end
            // END: virtual_interface_lookup_mod_ts1755007836817

            module_selection module_selection_inst_1755007836817_4277 (
                .out_part_select(inj_out_part_select_1755007836817_443),
                .out_vector_assign(inj_out_vector_assign_1755007836817_156),
                .in_bit(reset),
                .in_index(inj_in_index_1755007836817_355),
                .in_part_lsb(inj_in_part_lsb_1755007836817_329),
                .in_vector(inj_in_vector_1755007836817_498),
                .out_bit_select(inj_out_bit_select_1755007836817_284),
                .out_bitwise_ops(inj_out_bitwise_ops_1755007836817_399)
            );
        always @(posedge clk) begin
            inj_x_bb_1755007836816_636 <= inj_a_bb_1755007836816_562 + inj_b_bb_1755007836816_964;
            inj_y_bb_1755007836816_487 <= inj_x_bb_1755007836816_636 - inj_c_bb_1755007836816_660;
            inj_z_bb_1755007836816_54 <= inj_a_bb_1755007836816_562 * inj_c_bb_1755007836816_660;
        end
        // END: split_combo_nb_ts1755007836816

        hierarchy_if hierarchy_if_inst_1755007836815_3397 (
            .clk(clk),
            .main_in(inj_main_in_1755007836815_478),
            .main_out(inj_main_out_1755007836815_777)
        );
    assign processed_wide_ts1755007836814 = inj_wide_in_1755007836814_310 * 2;
    assign inj_upper_byte_out_1755007836814_297 = processed_wide_ts1755007836814[31:24];
    assign inj_lower_byte_out_1755007836814_277 = processed_wide_ts1755007836814[7:0];
    // END: part_select_ops_ts1755007836815

    super_outside_class_diag_mod super_outside_class_diag_mod_inst_1755007836814_1528 (
        .in_val(inj_in_val_1755007836814_31),
        .out_val(inj_out_val_1755007836814_740)
    );
endmodule

