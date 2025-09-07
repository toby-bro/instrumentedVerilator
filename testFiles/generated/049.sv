interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module ModClockedConditional (
    input logic clk,
    input logic data_in,
    input logic enable,
    output logic data_out
);
    logic reg_data;
    always @(posedge clk) begin
    if (enable) begin
        reg_data <= data_in;
    end
    end
    assign data_out = reg_data;
endmodule

module div_mod_ops (
    input logic [7:0] denominator,
    input logic [15:0] dividend_mod,
    input logic [7:0] divisor_mod,
    input logic [15:0] numerator,
    output logic [15:0] quotient,
    output logic [7:0] remainder
);
    assign quotient = (denominator == 0) ? 16'hFFFF : (numerator / denominator); 
    assign remainder = (divisor_mod == 0) ? 8'hFF : (dividend_mod % divisor_mod);
endmodule

module invalid_this_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module module_packed_logic (
    input logic data_in_in_pl,
    input logic [9:0] data_in_pl,
    output logic [4:0] data_out_pl
);
    logic [15:0] my_packed_logic ;
    always_comb begin
        my_packed_logic[9:0] = data_in_pl;
        my_packed_logic[15:10] = 6'h3F;
        my_packed_logic[0] = data_in_in_pl;
    end
    assign data_out_pl[4:1] = my_packed_logic[4:1];
    assign data_out_pl[0] = my_packed_logic[1];
endmodule

module more_ops (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    output logic anded,
    output logic diff,
    output logic ored,
    output logic [7:0] sum,
    output logic xored
);
    assign sum = a + b;
    assign diff = a > c;
    assign anded = a & b;
    assign ored = a | c;
    assign xored = a ^ b;
endmodule

module module_case_write (
    input logic [7:0] data_case_a,
    input logic [7:0] data_case_b,
    input logic [1:0] select_case,
    output logic case_output_ready
);
    my_if case_vif_inst();
    always_comb begin
        case (select_case)
            2'b00: begin
                case_vif_inst.data = 8'hAA;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b0;
            end
            2'b01: begin
                case_vif_inst.data = data_case_a;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b1;
            end
            2'b10: begin
                case_vif_inst.data = data_case_b;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b1;
            end
            default: begin
                case_vif_inst.data = 8'hFF;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b0;
            end
        endcase
        case_output_ready = case_vif_inst.ready;
    end
endmodule

module split_diff_vars_branches (
    input logic clk_z,
    input logic condition_z,
    input logic [7:0] in1_z,
    input logic [7:0] in2_z,
    output logic [7:0] out1_z,
    output logic [7:0] out2_z
);
    always @(posedge clk_z) begin
        if (condition_z) begin
            out1_z <= in1_z;
        end else begin
            out2_z <= in2_z;
        end
    end
endmodule

module snippet #(
    parameter int WIDTH = 8
) (
    input wire clk,
    input logic [7:0] inj_c_1755007767772_297,
    input logic [1:0] inj_case_expr_1755007767768_956,
    input logic [3:0] inj_case_inside_val_1755007767810_199,
    input bit [7:0] inj_data1_1755007767806_203,
    input bit [7:0] inj_data2_1755007767806_446,
    input logic [7:0] inj_data_case_a_1755007767769_847,
    input logic [7:0] inj_data_case_b_1755007767769_376,
    input logic [9:0] inj_data_in_pl_1755007767817_160,
    input logic [15:0] inj_dividend_mod_1755007767774_658,
    input wire [3:0] inj_in0_1755007767776_378,
    input wire [3:0] inj_in1_1755007767776_170,
    input wire [3:0] inj_in2_1755007767776_96,
    input wire [3:0] inj_in3_1755007767776_505,
    input int inj_in_val_1755007767777_518,
    input logic [15:0] inj_in_vec_1755007767773_536,
    input wire [1:0] inj_sel_1755007767776_463,
    input bit inj_sel_1755007767806_348,
    input logic inj_udnt_input_1755007767768_151,
    input logic inj_uin_1755007767768_245,
    input wire [15:0] inj_value1_1755007767770_15,
    input wire [15:0] inj_value2_1755007767770_776,
    input wire reset,
    output logic inj_anded_1755007767772_92,
    output logic inj_case_output_ready_1755007767769_759,
    output logic inj_data_out_1755007767784_788,
    output logic [4:0] inj_data_out_pl_1755007767817_18,
    output logic inj_diff_1755007767772_676,
    output wire inj_dout_1755007767779_55,
    output logic [7:0] inj_dout_1755007767825_158,
    output logic [4:0] inj_internal_out_1755007767768_133,
    output logic [4:0] inj_internal_out_1755007767810_587,
    output reg [3:0] inj_mux_out_1755007767776_126,
    output logic inj_o_1755007767794_66,
    output logic inj_o_1755007767821_687,
    output logic inj_ored_1755007767772_239,
    output logic [7:0] inj_out1_z_1755007767770_117,
    output logic [7:0] inj_out2_z_1755007767770_523,
    output wire inj_out_1755007767786_913,
    output logic [7:0] inj_out_1755007767797_556,
    output logic inj_out_b_1755007767771_179,
    output logic [7:0] inj_out_case_a_1755007767799_389,
    output logic [7:0] inj_out_case_b_1755007767799_671,
    output logic inj_out_e_1755007767769_919,
    output logic [7:0] inj_out_slice_be_1755007767773_759,
    output logic [7:0] inj_out_slice_le_1755007767773_836,
    output logic [7:0] inj_out_sum_1755007767803_79,
    output int inj_out_val_1755007767777_199,
    output int inj_out_val_1755007767781_216,
    output int inj_out_val_1755007767788_748,
    output logic inj_protected_active_1755007767769_611,
    output logic inj_q_1755007767790_153,
    output logic [15:0] inj_quotient_1755007767774_94,
    output logic [7:0] inj_remainder_1755007767774_471,
    output bit [7:0] inj_result1_1755007767806_807,
    output bit [7:0] inj_result2_1755007767806_121,
    output reg [15:0] inj_result_val_1755007767770_629,
    output logic [7:0] inj_sum_1755007767772_263,
    output logic inj_sum_1755007767792_486,
    output logic inj_udnt_output_1755007767768_304,
    output logic inj_uout_1755007767768_630,
    output logic inj_xored_1755007767772_908
);
    // BEGIN: udnt_port_module_ts1755007767768
    // BEGIN: case_unique0_violating_mod_ts1755007767768
    // BEGIN: PragmaProtectBoundaries_ts1755007767769
logic internal_state_ts1755007767769;
    // BEGIN: LintUnusedSignal_ts1755007767772
    logic unused_w_ts1755007767772; 
        // BEGIN: ContinuousWire_ts1755007767779
        wire internal_w_ts1755007767779;
            // BEGIN: mod_split_case_ts1755007767800
            logic [7:0]  split_case_var_ts1755007767799;
            logic [7:0] other_case_var_ts1755007767799;
                // BEGIN: simple_for_loop_ts1755007767803
                logic [7:0] sum_ts1755007767803;
                    // BEGIN: Parameterized_ts1755007767826
                    assign inj_dout_1755007767825_158 = other_case_var_ts1755007767799;
                    // END: Parameterized_ts1755007767826

                    // BEGIN: child_module_v2_config_dummy_ts1755007767821
                    assign inj_o_1755007767821_687 = unused_w_ts1755007767772 | unused_w_ts1755007767772; 
                    // END: child_module_v2_config_dummy_ts1755007767821

                    module_packed_logic module_packed_logic_inst_1755007767817_6247 (
                        .data_out_pl(inj_data_out_pl_1755007767817_18),
                        .data_in_in_pl(inj_uin_1755007767768_245),
                        .data_in_pl(inj_data_in_pl_1755007767817_160)
                    );
                    // BEGIN: case_priority_casex_complex_mod_ts1755007767811
                    always @* begin
                        priority casex ({inj_case_expr_1755007767768_956, inj_case_inside_val_1755007767810_199[1:0]})
                            4'b1???: inj_internal_out_1755007767810_587 = 24;
                            4'b?1??: inj_internal_out_1755007767810_587 = 25;  
                            4'b??1?: inj_internal_out_1755007767810_587 = 26;  
                            4'b???1: inj_internal_out_1755007767810_587 = 27;  
                            4'b0000: inj_internal_out_1755007767810_587 = 28;  
                            default: inj_internal_out_1755007767810_587 = 29;
                        endcase
                    end
                    // END: case_priority_casex_complex_mod_ts1755007767811

                    // BEGIN: comb_conditional_ts1755007767806
                    always @* begin
                        if (inj_sel_1755007767806_348) begin
                            inj_result1_1755007767806_807 = inj_data1_1755007767806_203;
                            inj_result2_1755007767806_121 = inj_data1_1755007767806_203;
                        end else begin
                            inj_result1_1755007767806_807 = inj_data2_1755007767806_446;
                            inj_result2_1755007767806_121 = inj_data2_1755007767806_446;
                        end
                    end
                    // END: comb_conditional_ts1755007767806

                always_comb begin
                    sum_ts1755007767803 = 8'h00;
                    for (int i = 0; i < 5; i = i + 1) begin
                        sum_ts1755007767803 = sum_ts1755007767803 + inj_c_1755007767772_297;
                    end
                    inj_out_sum_1755007767803_79 = sum_ts1755007767803;
                end
                // END: simple_for_loop_ts1755007767803

            always_comb begin
                split_case_var_ts1755007767799 = 8'hFF;
                other_case_var_ts1755007767799 = 8'hAA;
                case (inj_case_expr_1755007767768_956)
                    2'b00: begin
                        split_case_var_ts1755007767799 = inj_data_case_b_1755007767769_376 + 5;
                        other_case_var_ts1755007767799 = inj_data_case_b_1755007767769_376 + 6;
                    end
                    2'b01: begin
                        split_case_var_ts1755007767799 = inj_data_case_b_1755007767769_376 - 5;
                        other_case_var_ts1755007767799 = inj_data_case_b_1755007767769_376 - 6;
                    end
                    default: begin
                        split_case_var_ts1755007767799 = inj_data_case_b_1755007767769_376;
                        other_case_var_ts1755007767799 = inj_data_case_b_1755007767769_376;
                    end
                endcase
                inj_out_case_a_1755007767799_389 = split_case_var_ts1755007767799;
                inj_out_case_b_1755007767799_671 = other_case_var_ts1755007767799;
            end
            // END: mod_split_case_ts1755007767800

            // BEGIN: timed_assign_unhandled_ts1755007767797
            always @(posedge clk) begin
                inj_out_1755007767797_556 <= inj_data_case_a_1755007767769_847;
            end
            // END: timed_assign_unhandled_ts1755007767797

            // BEGIN: another_module_config_dummy_ts1755007767794
            assign inj_o_1755007767794_66 = inj_uin_1755007767768_245 & inj_uin_1755007767768_245; 
            // END: another_module_config_dummy_ts1755007767794

            // BEGIN: simple_adder_ts1755007767792
            assign inj_sum_1755007767792_486 = unused_w_ts1755007767772 + internal_state_ts1755007767769;
            // END: simple_adder_ts1755007767792

            // BEGIN: basic_d_flipflop_ts1755007767790
            always_ff @(posedge clk) begin
                inj_q_1755007767790_153 <= unused_w_ts1755007767772;
            end
            // END: basic_d_flipflop_ts1755007767790

            // BEGIN: undeclared_but_found_pkg_diag_mod_ts1755007767788
            assign inj_out_val_1755007767788_748 = inj_in_val_1755007767777_518;
            // END: undeclared_but_found_pkg_diag_mod_ts1755007767788

            // BEGIN: mod_simple_ts1755007767786
            assign inj_out_1755007767786_913 = reset;
            // END: mod_simple_ts1755007767786

            ModClockedConditional ModClockedConditional_inst_1755007767784_7417 (
                .enable(inj_udnt_input_1755007767768_151),
                .data_out(inj_data_out_1755007767784_788),
                .clk(clk),
                .data_in(internal_state_ts1755007767769)
            );
            // BEGIN: definition_used_diag_mod_ts1755007767781
            assign inj_out_val_1755007767781_216 = inj_in_val_1755007767777_518;
            // END: definition_used_diag_mod_ts1755007767781

        assign internal_w_ts1755007767779 = inj_udnt_input_1755007767768_151;
        assign inj_dout_1755007767779_55       = internal_w_ts1755007767779;
        // END: ContinuousWire_ts1755007767779

        invalid_this_diag_mod invalid_this_diag_mod_inst_1755007767777_3803 (
            .in_val(inj_in_val_1755007767777_518),
            .out_val(inj_out_val_1755007767777_199)
        );
        // BEGIN: Comb_Case_ts1755007767776
        always_comb begin
            case (inj_sel_1755007767776_463)
                2'b00: inj_mux_out_1755007767776_126 = inj_in0_1755007767776_378;
                2'b01: inj_mux_out_1755007767776_126 = inj_in1_1755007767776_170;
                2'b10: inj_mux_out_1755007767776_126 = inj_in2_1755007767776_96;
                default: inj_mux_out_1755007767776_126 = inj_in3_1755007767776_505;
            endcase
        end
        // END: Comb_Case_ts1755007767776

        div_mod_ops div_mod_ops_inst_1755007767774_2150 (
            .quotient(inj_quotient_1755007767774_94),
            .remainder(inj_remainder_1755007767774_471),
            .denominator(inj_c_1755007767772_297),
            .dividend_mod(inj_dividend_mod_1755007767774_658),
            .divisor_mod(inj_data_case_b_1755007767769_376),
            .numerator(inj_in_vec_1755007767773_536)
        );
        // BEGIN: range_select_simple_packed_ts1755007767773
        assign inj_out_slice_be_1755007767773_759 = inj_in_vec_1755007767773_536[7:0]; 
        assign inj_out_slice_le_1755007767773_836 = inj_in_vec_1755007767773_536[7:0]; 
        // END: range_select_simple_packed_ts1755007767773

        more_ops more_ops_inst_1755007767772_391 (
            .diff(inj_diff_1755007767772_676),
            .ored(inj_ored_1755007767772_239),
            .sum(inj_sum_1755007767772_263),
            .xored(inj_xored_1755007767772_908),
            .a(inj_data_case_a_1755007767769_847),
            .b(inj_data_case_b_1755007767769_376),
            .c(inj_c_1755007767772_297),
            .anded(inj_anded_1755007767772_92)
        );
    assign inj_out_b_1755007767771_179 = internal_state_ts1755007767769;
    // END: LintUnusedSignal_ts1755007767772

    // BEGIN: Comb_IfElse_ts1755007767771
    always_comb begin
        if (clk) begin
            inj_result_val_1755007767770_629 = inj_value1_1755007767770_15;
        end else begin
            inj_result_val_1755007767770_629 = inj_value2_1755007767770_776;
        end
    end
    // END: Comb_IfElse_ts1755007767771

    split_diff_vars_branches split_diff_vars_branches_inst_1755007767770_1181 (
        .out1_z(inj_out1_z_1755007767770_117),
        .out2_z(inj_out2_z_1755007767770_523),
        .clk_z(clk),
        .condition_z(internal_state_ts1755007767769),
        .in1_z(inj_data_case_b_1755007767769_376),
        .in2_z(inj_data_case_a_1755007767769_847)
    );
    module_case_write module_case_write_inst_1755007767769_5449 (
        .data_case_b(inj_data_case_b_1755007767769_376),
        .select_case(inj_case_expr_1755007767768_956),
        .case_output_ready(inj_case_output_ready_1755007767769_759),
        .data_case_a(inj_data_case_a_1755007767769_847)
    );
    // BEGIN: LintCombBlockAssign_ts1755007767769
    always_comb begin
        inj_out_e_1755007767769_919 = inj_udnt_input_1755007767768_151 & inj_uin_1755007767768_245;
    end
    // END: LintCombBlockAssign_ts1755007767769

`ifdef SLANG_PRAGMA
`protect begin
`endif
assign internal_state_ts1755007767769 = inj_uin_1755007767768_245;
`ifdef SLANG_PRAGMA
`protect end
`endif
`ifdef SLANG_PRAGMA
`protect begin_protected
`endif
`ifdef SLANG_PRAGMA
`protect end_protected
`endif
assign inj_protected_active_1755007767769_611 = internal_state_ts1755007767769;
    // END: PragmaProtectBoundaries_ts1755007767769

    always @* begin
        unique0 casez (inj_case_expr_1755007767768_956)
            2'b1?: inj_internal_out_1755007767768_133 = 8;
            2'b11: inj_internal_out_1755007767768_133 = 9;  
            2'b?1: inj_internal_out_1755007767768_133 = 10; 
            2'b00: inj_internal_out_1755007767768_133 = 11; 
        endcase
    end
    // END: case_unique0_violating_mod_ts1755007767768

    assign inj_uout_1755007767768_630 = inj_uin_1755007767768_245;
    assign inj_udnt_output_1755007767768_304 = inj_udnt_input_1755007767768_151;
    // END: udnt_port_module_ts1755007767768
endmodule

