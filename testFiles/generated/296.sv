module ArrayIndexAndPartSelect (
    input logic [31:0] data_in,
    input int index_in,
    input logic [4:0] start_bit,
    output logic bit_out,
    output logic [7:0] byte_out
);
    logic [31:0] internal_data = data_in;
    assign bit_out = internal_data[index_in];
    assign byte_out = internal_data[start_bit +: 8];
endmodule

module DummyHierModule (
    input bit in_bit,
    output logic out_logic
);
    assign out_logic = in_bit;
endmodule

module Mod_ArrayOps (
    input wire [1:0] in_const_index,
    input wire [7:0] in_data,
    input wire [1:0] in_index,
    output logic [7:0] out_array_sel_const,
    output logic [7:0] out_array_sel_var
);
    logic [7:0] my_array [3:0];
    always_comb begin
        my_array[0] = in_data;
        my_array[1] = in_data + 8'd1;
        my_array[2] = in_data + 8'd2;
        my_array[3] = in_data + 8'd3;
        out_array_sel_var = my_array[in_index];
        out_array_sel_const = my_array[in_const_index];
    end
endmodule

module definition_used_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module split_if_only_then (
    input logic clk_h,
    input logic condition_h,
    input logic [7:0] in_val_h,
    output logic [7:0] out_reg_h
);
    always @(posedge clk_h) begin
        if (condition_h) begin
            out_reg_h <= in_val_h;
        end
    end
endmodule

module snippet #(
    parameter bit GEN = 1
) (
    input wire clk,
    input logic inj_cond_dd_1755007854138_706,
    input logic [31:0] inj_data_in_1755007854152_909,
    input bit [3:0] inj_in1_1755007854137_330,
    input logic [7:0] inj_in1_dd_1755007854138_761,
    input bit [3:0] inj_in2_1755007854137_914,
    input logic [7:0] inj_in2_dd_1755007854138_863,
    input logic [7:0] inj_in3_dd_1755007854137_723,
    input logic [7:0] inj_in4_dd_1755007854138_415,
    input bit inj_in_bit_1755007854166_701,
    input wire [1:0] inj_in_const_index_1755007854162_712,
    input wire [7:0] inj_in_data_1755007854162_51,
    input wire [1:0] inj_in_index_1755007854162_690,
    input logic inj_in_j_1755007854140_370,
    input int inj_in_val_1755007854137_1,
    input logic [3:0] inj_in_vector_1755007854136_406,
    input logic [4:0] inj_start_bit_1755007854152_425,
    input wire reset,
    output logic inj_bit_out_1755007854152_742,
    output logic [7:0] inj_byte_out_1755007854152_949,
    output logic [7:0] inj_data_out_1755007854145_824,
    output logic inj_is_even_1755007854138_676,
    output logic inj_o_out_1755007854147_893,
    output logic inj_o_reg_out_1755007854158_906,
    output logic inj_o_sum_1755007854150_607,
    output wire inj_o_wire_out_1755007854158_165,
    output bit [3:0] inj_out1_1755007854137_322,
    output logic [7:0] inj_out1_dd_1755007854138_109,
    output bit [3:0] inj_out2_1755007854137_994,
    output logic [7:0] inj_out2_dd_1755007854138_72,
    output logic [7:0] inj_out_array_sel_const_1755007854162_111,
    output logic [7:0] inj_out_array_sel_var_1755007854162_672,
    output logic inj_out_l_1755007854140_592,
    output logic inj_out_logic_1755007854166_33,
    output logic [7:0] inj_out_reg_h_1755007854155_126,
    output logic inj_out_single_1755007854136_653,
    output logic inj_out_sub_1755007854139_50,
    output int inj_out_val_1755007854137_827,
    output logic [7:0] inj_out_var_1755007854142_874,
    output logic inj_sig_out_1755007854140_704,
    output logic [7:0] inj_wide_reg_1755007854150_794
);
    // BEGIN: combinatorial_logic_ts1755007854137
    // BEGIN: ModuleFF_ts1755007854137
    parameter int MAX_COUNT = 10;
    localparam int START_VAL = 5;
    logic [3:0] ff_reg_ts1755007854137;
    integer unused_int_var_ts1755007854137;
        // BEGIN: not_a_hierarchical_scope_diag_mod_ts1755007854143
        logic [7:0] simple_var_nahsdm_ts1755007854143;
            // BEGIN: SequentialLogic_ts1755007854145
            logic [7:0] internal_reg_ts1755007854145;
                // BEGIN: name_conflict_example_ts1755007854148
                parameter int my_param = 5;
                logic my_var_ts1755007854147;
                    // BEGIN: mod_lint_target_ts1755007854150
                    logic l_reg_ts1755007854150;
                        // BEGIN: nets_alias_clocking_ts1755007854159
                        wire  w_internal_ts1755007854159;
                        logic r_internal_ts1755007854159;
                            DummyHierModule DummyHierModule_inst_1755007854166_9001 (
                                .in_bit(inj_in_bit_1755007854166_701),
                                .out_logic(inj_out_logic_1755007854166_33)
                            );
                            Mod_ArrayOps Mod_ArrayOps_inst_1755007854162_369 (
                                .out_array_sel_var(inj_out_array_sel_var_1755007854162_672),
                                .in_const_index(inj_in_const_index_1755007854162_712),
                                .in_data(inj_in_data_1755007854162_51),
                                .in_index(inj_in_index_1755007854162_690),
                                .out_array_sel_const(inj_out_array_sel_const_1755007854162_111)
                            );
                        assign w_internal_ts1755007854159  = reset & l_reg_ts1755007854150;
                        assign inj_o_wire_out_1755007854158_165  = w_internal_ts1755007854159;
                        always_ff @(posedge clk) r_internal_ts1755007854159 <= inj_in_j_1755007854140_370;
                        assign inj_o_reg_out_1755007854158_906 = r_internal_ts1755007854159;
                        // END: nets_alias_clocking_ts1755007854159

                        split_if_only_then split_if_only_then_inst_1755007854155_5654 (
                            .clk_h(clk),
                            .condition_h(inj_in_j_1755007854140_370),
                            .in_val_h(simple_var_nahsdm_ts1755007854143),
                            .out_reg_h(inj_out_reg_h_1755007854155_126)
                        );
                        ArrayIndexAndPartSelect ArrayIndexAndPartSelect_inst_1755007854152_3555 (
                            .start_bit(inj_start_bit_1755007854152_425),
                            .bit_out(inj_bit_out_1755007854152_742),
                            .byte_out(inj_byte_out_1755007854152_949),
                            .data_in(inj_data_in_1755007854152_909),
                            .index_in(inj_in_val_1755007854137_1)
                        );
                    always_comb begin
                        l_reg_ts1755007854150 = 1;
                        inj_wide_reg_1755007854150_794 = {clk, reset};
                    end
                    assign inj_o_sum_1755007854150_607 = clk + reset;
                    // END: mod_lint_target_ts1755007854150

                always_comb my_var_ts1755007854147 = inj_in_j_1755007854140_370;
                assign inj_o_out_1755007854147_893 = inj_in_j_1755007854140_370 && (my_param == 5) && my_var_ts1755007854147;
                // END: name_conflict_example_ts1755007854148

            always @(posedge clk or negedge reset) begin
                if (~reset) begin
                    internal_reg_ts1755007854145 <= 8'h00;
                end else begin
                    internal_reg_ts1755007854145 <= inj_in2_dd_1755007854138_863;
                end
            end
            assign inj_data_out_1755007854145_824 = internal_reg_ts1755007854145;
            // END: SequentialLogic_ts1755007854145

        always_comb simple_var_nahsdm_ts1755007854143 = inj_in3_dd_1755007854137_723;
        assign inj_out_var_1755007854142_874 = simple_var_nahsdm_ts1755007854143;
        // END: not_a_hierarchical_scope_diag_mod_ts1755007854143

        // BEGIN: GenerateIfParam_ts1755007854140
        generate
            if (GEN) begin : g_true
                assign inj_sig_out_1755007854140_704 = inj_cond_dd_1755007854138_706;
            end
            else begin : g_false
                assign inj_sig_out_1755007854140_704 = ~inj_cond_dd_1755007854138_706;
            end
        endgenerate
        // END: GenerateIfParam_ts1755007854140

        // BEGIN: LintLatch_ts1755007854140
        always_comb begin
            if (inj_in_j_1755007854140_370) begin
                inj_out_l_1755007854140_592 = inj_cond_dd_1755007854138_706;
            end else begin
                inj_out_l_1755007854140_592 = 1'b0; 
            end
        end
        // END: LintLatch_ts1755007854140

        // BEGIN: mod_sub_ts1755007854139
        assign inj_out_sub_1755007854139_50 = clk;
        // END: mod_sub_ts1755007854139

        // BEGIN: FunctionTaskMod_ts1755007854138
        function automatic bit check_even(input logic [7:0] v);
            check_even = ~v[0];
        endfunction
        task automatic dummy_task(input logic [7:0] v);
            int tmp_ts1755007854138;
            tmp_ts1755007854138 = v;
        endtask
        assign inj_is_even_1755007854138_676 = check_even(inj_in2_dd_1755007854138_863);
        // END: FunctionTaskMod_ts1755007854138

        // BEGIN: split_multi_nb_in_if_ts1755007854138
        always @(posedge clk) begin
            if (inj_cond_dd_1755007854138_706) begin
                inj_out1_dd_1755007854138_109 <= inj_in1_dd_1755007854138_761 + inj_in2_dd_1755007854138_863;
                inj_out2_dd_1755007854138_72 <= inj_in3_dd_1755007854137_723 - inj_in4_dd_1755007854138_415;
            end else begin
                inj_out1_dd_1755007854138_109 <= inj_in1_dd_1755007854138_761 * inj_in2_dd_1755007854138_863;
                inj_out2_dd_1755007854138_72 <= inj_in3_dd_1755007854137_723 / (inj_in4_dd_1755007854138_415 + 1);
            end
        end
        // END: split_multi_nb_in_if_ts1755007854138

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            ff_reg_ts1755007854137 <= START_VAL;
            inj_out1_1755007854137_322 <= '0;
            inj_out2_1755007854137_994 <= '0;
            unused_int_var_ts1755007854137 <= 0;
        end else begin
            case ({inj_in1_1755007854137_330, inj_in2_1755007854137_914})
                8'h00: ff_reg_ts1755007854137 <= ff_reg_ts1755007854137;
                8'h01: ff_reg_ts1755007854137 <= inj_in1_1755007854137_330 + inj_in2_1755007854137_914;
                default: ff_reg_ts1755007854137 <= MAX_COUNT;
            endcase
            inj_out1_1755007854137_322 <= ff_reg_ts1755007854137;
            inj_out2_1755007854137_994 <= {inj_in1_1755007854137_330[0], inj_in1_1755007854137_330[0], inj_in1_1755007854137_330[0], inj_in1_1755007854137_330[0]} | {inj_in2_1755007854137_914[3], inj_in2_1755007854137_914[2], inj_in2_1755007854137_914[1], inj_in2_1755007854137_914[0]};
        end
    end
    // END: ModuleFF_ts1755007854137

    definition_used_diag_mod definition_used_diag_mod_inst_1755007854137_4171 (
        .in_val(inj_in_val_1755007854137_1),
        .out_val(inj_out_val_1755007854137_827)
    );
    always_comb begin
        if (inj_in_vector_1755007854136_406 > 4'd5) begin
            inj_out_single_1755007854136_653 = 1'b1;
        end else begin
            inj_out_single_1755007854136_653 = 1'b0;
        end
    end
    // END: combinatorial_logic_ts1755007854137
endmodule

