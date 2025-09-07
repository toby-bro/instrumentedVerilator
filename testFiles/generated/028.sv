interface MyInterface (
    input logic clk
);
    logic req;
    logic valid;
    modport master (output req, input valid, input clk);
    modport slave (input req, output valid, input clk);
endinterface
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

module mod_fixup_target (
    input logic fs_in_target,
    output logic fs_out_target
);
    assign fs_out_target = fs_in_target;
endmodule

module module_finish_numbers (
    input bit dummy_in,
    output bit dummy_out
);
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
    assign dummy_out = dummy_in;
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module snippet (
    input wire clk,
    input bit inj_dummy_in_1755007759809_994,
    input logic inj_i_data_sync_1755007759794_886,
    input logic inj_i_reg_data_1755007759794_807,
    input logic [31:0] inj_in1_1755007759797_466,
    input logic [31:0] inj_in2_1755007759797_683,
    input wire [2:0] inj_in_index_1755007759793_730,
    input wire [1:0] inj_in_index_1755007759795_640,
    input wire [1:0] inj_in_part_lsb_1755007759793_974,
    input logic [1:0] inj_in_val_1755007759805_79,
    input wire [7:0] inj_in_vector_1755007759793_71,
    input int inj_input_int_1755007759795_197,
    input wire reset,
    output reg inj_data_out_1755007759800_602,
    output bit inj_dummy_out_1755007759809_669,
    output logic inj_fs_out_target_1755007759794_680,
    output logic inj_o_out_1755007759801_926,
    output logic inj_o_out_1755007759807_334,
    output logic inj_o_reg_out_1755007759794_290,
    output wire inj_o_wire_out_1755007759794_195,
    output logic [31:0] inj_out_1755007759797_489,
    output bit inj_out_1755007759811_696,
    output logic [7:0] inj_out_array_sel_const_1755007759795_962,
    output logic [7:0] inj_out_array_sel_var_1755007759795_194,
    output logic inj_out_bit_select_1755007759793_492,
    output logic [7:0] inj_out_bitwise_ops_1755007759793_800,
    output logic inj_out_o_1755007759793_714,
    output logic [3:0] inj_out_part_select_1755007759793_114,
    output reg inj_out_res_1755007759805_192,
    output logic [7:0] inj_out_v_1755007759799_692,
    output int inj_out_val_1755007759803_543,
    output logic [7:0] inj_out_vector_assign_1755007759793_175,
    output int inj_output_int_1755007759795_51,
    output logic inj_valid_out_1755007759796_295
);
    // BEGIN: module_selection_ts1755007759793
    // BEGIN: mod_internal_if_test_ts1755007759793
    // BEGIN: nets_alias_clocking_ts1755007759794
    wire  w_internal_ts1755007759794;
    logic r_internal_ts1755007759794;
        // BEGIN: func_macro_args_ts1755007759795
        `define ADD(a, b)       ((a) + (b))
        `define SUBTRACT(x, y)  ((x) - (y))
        localparam int P1_ADD = `ADD(10, 20);
        int p2_sub_var_ts1755007759795;
            // BEGIN: Mod_ArrayOps_ts1755007759796
            logic [7:0] my_array_ts1755007759796 [3:0];
                // BEGIN: named_block_logic_ts1755007759802
                logic r_internal_ts1755007759801;
                logic r_temp_ts1755007759801;
                    // BEGIN: attributes_on_expr_port_ts1755007759807
                    logic internal_sig_ts1755007759807;
                        // BEGIN: BindSimpleModule_ts1755007759811
                        assign inj_out_1755007759811_696 = inj_dummy_in_1755007759809_994;
                        // END: BindSimpleModule_ts1755007759811

                        module_finish_numbers module_finish_numbers_inst_1755007759809_8257 (
                            .dummy_in(inj_dummy_in_1755007759809_994),
                            .dummy_out(inj_dummy_out_1755007759809_669)
                        );
                    assign internal_sig_ts1755007759807 = r_internal_ts1755007759801 & r_temp_ts1755007759801;
                    simple_adder sa_inst(
                        .a  (r_internal_ts1755007759801),
                        (* fanout_limit = 10 *) .b(r_temp_ts1755007759801),
                        .sum(inj_o_out_1755007759807_334)
                    );
                    // END: attributes_on_expr_port_ts1755007759807

                    case_empty_statement case_empty_statement_inst_1755007759805_52 (
                        .in_val(inj_in_val_1755007759805_79),
                        .out_res(inj_out_res_1755007759805_192)
                    );
                    // BEGIN: local_not_allowed_diag_mod_ts1755007759803
                    assign inj_out_val_1755007759803_543 = inj_input_int_1755007759795_197;
                    // END: local_not_allowed_diag_mod_ts1755007759803

                always_comb begin : my_combinational_block
                    r_temp_ts1755007759801 = inj_i_reg_data_1755007759794_807 & r_internal_ts1755007759794;
                    r_internal_ts1755007759801 = r_temp_ts1755007759801;
                    inj_o_out_1755007759801_926 = r_internal_ts1755007759801;
                end
                // END: named_block_logic_ts1755007759802

                // BEGIN: mod_event_posedge_ts1755007759800
                always @(posedge clk) begin
                    inj_data_out_1755007759800_602 <= w_internal_ts1755007759794;
                end
                // END: mod_event_posedge_ts1755007759800

                // BEGIN: ModVectorAdd_ts1755007759799
                assign inj_out_v_1755007759799_692 = my_array_ts1755007759796 + 8'h01;
                // END: ModVectorAdd_ts1755007759799

                // BEGIN: always_comb_if_ts1755007759797
                always_comb begin
                    if (inj_i_reg_data_1755007759794_807) begin
                        inj_out_1755007759797_489 = inj_in1_1755007759797_466;
                    end else begin
                        inj_out_1755007759797_489 = inj_in2_1755007759797_683;
                    end
                end
                // END: always_comb_if_ts1755007759797

                // BEGIN: ModuleWithInterface_ts1755007759796
                MyInterface my_if (clk);
                assign my_if.req = 1'b1;
                assign inj_valid_out_1755007759796_295 = my_if.valid;
                // END: ModuleWithInterface_ts1755007759796

            always_comb begin
                my_array_ts1755007759796[0] = inj_in_vector_1755007759793_71;
                my_array_ts1755007759796[1] = inj_in_vector_1755007759793_71 + 8'd1;
                my_array_ts1755007759796[2] = inj_in_vector_1755007759793_71 + 8'd2;
                my_array_ts1755007759796[3] = inj_in_vector_1755007759793_71 + 8'd3;
                inj_out_array_sel_var_1755007759795_194 = my_array_ts1755007759796[inj_in_index_1755007759795_640];
                inj_out_array_sel_const_1755007759795_962 = my_array_ts1755007759796[inj_in_part_lsb_1755007759793_974];
            end
            // END: Mod_ArrayOps_ts1755007759796

        always_comb begin
            p2_sub_var_ts1755007759795 = `SUBTRACT(50, inj_input_int_1755007759795_197);
        end
        assign inj_output_int_1755007759795_51 = P1_ADD + p2_sub_var_ts1755007759795;
        // END: func_macro_args_ts1755007759795

        mod_fixup_target mod_fixup_target_inst_1755007759794_3171 (
            .fs_out_target(inj_fs_out_target_1755007759794_680),
            .fs_in_target(inj_i_data_sync_1755007759794_886)
        );
    assign w_internal_ts1755007759794  = clk & inj_i_reg_data_1755007759794_807;
    assign inj_o_wire_out_1755007759794_195  = w_internal_ts1755007759794;
    always_ff @(posedge clk) r_internal_ts1755007759794 <= inj_i_data_sync_1755007759794_886;
    assign inj_o_reg_out_1755007759794_290 = r_internal_ts1755007759794;
    // END: nets_alias_clocking_ts1755007759794

    assign inj_out_o_1755007759793_714 = !reset;
    // END: mod_internal_if_test_ts1755007759793

    always_comb begin
    inj_out_vector_assign_1755007759793_175 = inj_in_vector_1755007759793_71;
    inj_out_bit_select_1755007759793_492 = inj_in_vector_1755007759793_71[inj_in_index_1755007759793_730];
    inj_out_part_select_1755007759793_114 = inj_in_vector_1755007759793_71[inj_in_part_lsb_1755007759793_974 +: 4];
    inj_out_bitwise_ops_1755007759793_800 = inj_in_vector_1755007759793_71 & {8{reset}};
    end
    // END: module_selection_ts1755007759793
endmodule

