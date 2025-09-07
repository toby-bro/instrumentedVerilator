module CombinationalLogicExplicit (
    input logic [15:0] data0,
    input logic [15:0] data1,
    input logic sel,
    output logic [15:0] data_out
);
    always @(sel or data0 or data1) begin
        if (sel) begin
            data_out = data1;
        end else begin
            data_out = data0;
        end
    end
endmodule

module MiscExpressions_ValueRange (
    input logic [15:0] in_vector,
    output logic [7:0] out_slice
);
    always_comb begin
        out_slice = in_vector[7:0];
    end
endmodule

module ModMultipleAlways (
    input logic clk_a,
    input logic clk_b,
    input logic din_a,
    input logic din_b,
    input logic rst_n,
    output logic dout_a,
    output logic dout_b
);
    always @(posedge clk_a or negedge rst_n) begin 
    if (!rst_n) begin 
        dout_a <= 1'b0;
    end else begin
        dout_a <= din_a; 
    end
    end
    always @(posedge clk_b) begin 
    dout_b <= din_b; 
    end
endmodule

module ModuleBasic (
    input logic a,
    input int b,
    output logic out_a,
    output int out_b
);
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c;
    int   d;
    always_comb begin
        logic temp_v;
        temp_v = d;
        c      = temp_v;
    end
    assign out_a = a;
    assign d     = b;
    assign out_b = d + P1 + LP1;
endmodule

module Parameterized #(
    parameter int WIDTH = 8
) (
    input logic [7:0] din,
    output logic [7:0] dout
);
    assign dout = din;
endmodule

module StructExample (
    input logic [15:0] in_data,
    output logic [7:0] out_field_a,
    output logic [7:0] out_field_b
);
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
    } example_struct_t;
    example_struct_t my_struct;
    always_comb begin
        my_struct     = in_data;
        out_field_a   = my_struct.field_a;
        out_field_b   = my_struct.field_b;
    end
endmodule

module case_selector (
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [1:0] sel_in,
    output logic [3:0] data_out_case
);
    always_comb begin
        case (sel_in)
            2'b00: data_out_case = data0; 
            2'b01: data_out_case = data1; 
            2'b10: data_out_case = data2; 
            default: data_out_case = data3; 
        endcase
    end
endmodule

module child_concat_output (
    input logic dummy_in,
    output logic [7:0] data
);
    assign data = dummy_in ? 8'hAA : 8'h55;
endmodule

module configuration_top (
    input logic i_in,
    output logic o_out
);
    assign o_out = i_in;
endmodule

module mod_if_elseif_chained (
    input bit [7:0] in_value,
    output bit [2:0] out_category
);
always_comb begin
    if (in_value < 10) begin
        out_category = 3'd0;
    end else if (in_value < 50) begin
        out_category = 3'd1;
    end else if (in_value < 100) begin
        out_category = 3'd2;
    end else begin
        out_category = 3'd3;
    end
end
endmodule

module mod_logical_not (
    input logic cond_in,
    output logic cond_out
);
    always_comb begin
        cond_out = !cond_in;
    end
endmodule

module mod_split_nested (
    input logic clk,
    input logic cond1,
    input logic cond2,
    input logic [7:0] data_in,
    input logic reset,
    output logic [7:0] out_nested_a,
    output logic [7:0] out_nested_b
);
    logic [7:0]  split_nested_var;
    logic [7:0] other_nested_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_nested_var <= 8'b0;
            other_nested_var <= 8'b0;
        end else begin
            split_nested_var <= 8'h11; 
            other_nested_var <= 8'h22; 
            if (cond1) begin
                split_nested_var <= data_in + 10;
                other_nested_var <= data_in + 20;
                if (cond2) begin
                    split_nested_var <= data_in + 100;
                    other_nested_var <= data_in + 200;
                end
            end else begin
                split_nested_var <= data_in - 10;
                other_nested_var <= data_in - 20;
            end
        end
    end
    always_comb begin
        out_nested_a = split_nested_var;
        out_nested_b = other_nested_var;
    end
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

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
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

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module bind_directive_top (
    input logic i_clk,
    input logic [3:0] i_control,
    input logic [7:0] i_data,
    output logic [7:0] o_result,
    output logic o_status
);
    target_module_for_bind target_inst(
        .i_target_clk   (i_clk),
        .i_target_data  (i_data),
        .o_target_result(o_result)
    );
    module_to_bind bind_inst(
        .i_bind_clk     (i_clk),
        .i_bind_control (i_control),
        .o_bind_status  (o_status)
    );
endmodule

module snippet #(
    parameter bit GEN = 1,
    parameter int SEL_PARAM = 6
) (
    input wire clk,
    input logic inj_cond1_1755007826640_506,
    input logic inj_cond2_1755007826640_38,
    input logic [3:0] inj_data1_1755007826665_358,
    input logic [15:0] inj_data1_1755007826681_731,
    input logic [3:0] inj_data2_1755007826665_33,
    input logic [3:0] inj_data3_1755007826665_817,
    input logic [7:0] inj_data_in_1755007826640_804,
    input logic [3:0] inj_data_in_1755007826649_671,
    input logic [9:0] inj_data_in_pl_1755007826641_476,
    input wire [1:0] inj_i_sel_1755007826673_383,
    input wire [3:0] inj_i_val_1755007826673_479,
    input bit [7:0] inj_in1_1755007826640_450,
    input bit [7:0] inj_in2_1755007826640_656,
    input logic [7:0] inj_in2_1755007826650_980,
    input logic [7:0] inj_in3_1755007826650_452,
    input logic [15:0] inj_in_data_1755007826659_929,
    input wire [7:0] inj_in_latch_data_1755007826800_972,
    input int inj_in_val_1755007826645_206,
    input logic [2:0] inj_selector_1755007826642_243,
    input logic [63:0] inj_wide_a_1755007826741_677,
    input logic [63:0] inj_wide_b_1755007826741_915,
    input logic [63:0] inj_wide_c_1755007826741_137,
    input wire [31:0] inj_wide_in_1755007826773_81,
    input wire reset,
    output logic inj_cond_out_1755007826695_846,
    output logic [7:0] inj_data_1755007826782_189,
    output logic [3:0] inj_data_out_1755007826649_494,
    output logic [7:0] inj_data_out_1755007826656_674,
    output logic [15:0] inj_data_out_1755007826681_719,
    output logic [3:0] inj_data_out_case_1755007826665_31,
    output logic [4:0] inj_data_out_pl_1755007826641_34,
    output logic [7:0] inj_dout_1755007826714_554,
    output logic inj_dout_a_1755007826644_594,
    output logic inj_dout_b_1755007826644_419,
    output logic [7:0] inj_final_val_1755007826652_17,
    output logic [7:0] inj_left_shift_log_1755007826701_299,
    output wire [7:0] inj_lower_byte_out_1755007826773_508,
    output logic inj_nand_out_1755007826650_671,
    output logic inj_nor_out_1755007826650_171,
    output logic inj_o_1755007826670_332,
    output logic inj_o_done_1755007826722_683,
    output logic inj_o_out_1755007826643_816,
    output logic [3:0] inj_o_out_1755007826673_983,
    output logic [7:0] inj_o_result_1755007826707_386,
    output logic inj_o_status_1755007826707_746,
    output bit [7:0] inj_out1_1755007826640_377,
    output logic inj_out1_1755007826641_16,
    output bit [7:0] inj_out2_1755007826640_978,
    output logic inj_out_c_1755007826677_179,
    output bit [2:0] inj_out_category_1755007826689_416,
    output logic [7:0] inj_out_data_1755007826728_441,
    output logic [7:0] inj_out_field_a_1755007826659_896,
    output logic [7:0] inj_out_field_b_1755007826659_582,
    output logic inj_out_l_1755007826646_90,
    output reg [7:0] inj_out_latch_reg_1755007826800_473,
    output logic [7:0] inj_out_nested_a_1755007826640_146,
    output logic [7:0] inj_out_nested_b_1755007826640_596,
    output logic inj_out_pd_1755007826647_204,
    output int inj_out_port_1755007826757_895,
    output reg inj_out_res_1755007826820_184,
    output logic [7:0] inj_out_slice_1755007826735_462,
    output int inj_out_val_1755007826645_25,
    output logic [7:0] inj_out_var_1755007826811_913,
    output logic inj_p2_1755007826662_507,
    output logic inj_p2_1755007826750_85,
    output logic [7:0] inj_result_and_1755007826654_433,
    output logic [7:0] inj_result_or_1755007826654_514,
    output logic [3:0] inj_result_out_1755007826642_811,
    output logic [7:0] inj_result_xor_1755007826654_693,
    output logic [7:0] inj_right_shift_arith_1755007826701_802,
    output logic [7:0] inj_right_shift_log_1755007826701_106,
    output logic inj_sig_out_1755007826685_658,
    output logic inj_sum_1755007826791_628,
    output logic [15:0] inj_sum_out_i_1755007826765_71,
    output wire [7:0] inj_upper_byte_out_1755007826773_43,
    output logic [63:0] inj_wide_out_1755007826741_361,
    output logic inj_xnor_out_1755007826650_215,
    output logic inj_y_1755007826643_361
);
    // BEGIN: comb_simple_ts1755007826640
    // BEGIN: ModuleLineDirective_ts1755007826641
    logic internal_sig_a_ts1755007826641;
    logic internal_sig_b_ts1755007826641;
    logic unused_line_var_ts1755007826641;
        // BEGIN: loop_with_internal_assign_ts1755007826652
        logic [7:0] current_val_ts1755007826652;
            // BEGIN: ModuleHierarchy_High_ts1755007826657
            ModuleBasic m1 (
                .a      (1'b1),
                .b      (inj_in_val_1755007826645_206),
                .out_a  (),
                .out_b  ( )
            );
            if (SEL_PARAM > 5) begin : gen_high
                int high_data_ts1755007826656;
                ModuleBasic m_high (
                    .a      (1'b0),
                    .b      (SEL_PARAM),
                    .out_a  (),
                    .out_b  (high_data_ts1755007826656)
                );
            end else begin : gen_low
                int low_data_ts1755007826656;
                ModuleBasic m_low (
                    .a      (1'b0),
                    .b      (SEL_PARAM),
                    .out_a  (),
                    .out_b  (low_data_ts1755007826656)
                );
            end
            for (genvar i = 0; i < 2; ++i) begin : gen_loop
                logic [1:0] sub_in_ts1755007826656;
                assign sub_in_ts1755007826656 = inj_data_in_1755007826649_671[i*2 +: 2];
                int temp_int_ts1755007826656;
                    // BEGIN: child_empty_ports_ts1755007826662
                    input logic inj_cond1_1755007826640_506_ts1755007826662;
                    output logic inj_p2_1755007826662_507_ts1755007826662;
                        // BEGIN: mod_case_block_attrs_ts1755007826673
                        logic [3:0] l_temp_ts1755007826673;
                            // BEGIN: mod_statement_block_var_ts1755007826677
                            always_comb begin : block_with_vars
                                int   block_local_int_ts1755007826677;
                                logic [7:0] block_local_logic_ts1755007826677;
                                    // BEGIN: mod_basic_ts1755007826722
                                    logic r_state_ts1755007826722;
                                        // BEGIN: child_empty_ports_ts1755007826750
                                        input logic inj_cond1_1755007826640_506_ts1755007826662_ts1755007826750;
                                        output logic inj_p2_1755007826750_85_ts1755007826750;
                                            // BEGIN: not_a_hierarchical_scope_diag_mod_ts1755007826811
                                            logic [7:0] simple_var_nahsdm_ts1755007826811;
                                                // BEGIN: case_empty_statement_ts1755007826821
                                                always_comb begin
                                                    inj_out_res_1755007826820_184 = 1'b0;
                                                    case (sub_in_ts1755007826656)
                                                        2'b00: inj_out_res_1755007826820_184 = 1'b1;
                                                        2'b01: ;
                                                        2'b10: inj_out_res_1755007826820_184 = 1'b0;
                                                        default: inj_out_res_1755007826820_184 = 1'b1;
                                                    endcase
                                                end
                                                // END: case_empty_statement_ts1755007826821

                                            always_comb simple_var_nahsdm_ts1755007826811 = current_val_ts1755007826652;
                                            assign inj_out_var_1755007826811_913 = simple_var_nahsdm_ts1755007826811;
                                            // END: not_a_hierarchical_scope_diag_mod_ts1755007826811

                                            // BEGIN: module_latch_ts1755007826800
                                            always_latch begin
                                            if (reset) begin
                                                inj_out_latch_reg_1755007826800_473 = inj_in_latch_data_1755007826800_972;
                                            end
                                            end
                                            // END: module_latch_ts1755007826800

                                            // BEGIN: simple_adder_ts1755007826791
                                            assign inj_sum_1755007826791_628 = inj_cond1_1755007826640_506_ts1755007826662 + inj_p2_1755007826750_85_ts1755007826750;
                                            // END: simple_adder_ts1755007826791

                                            child_concat_output child_concat_output_inst_1755007826782_4463 (
                                                .dummy_in(internal_sig_b_ts1755007826641),
                                                .data(inj_data_1755007826782_189)
                                            );
                                            part_select_ops part_select_ops_inst_1755007826773_9871 (
                                                .wide_in(inj_wide_in_1755007826773_81),
                                                .lower_byte_out(inj_lower_byte_out_1755007826773_508),
                                                .upper_byte_out(inj_upper_byte_out_1755007826773_43)
                                            );
                                            split_for_loop split_for_loop_inst_1755007826765_7068 (
                                                .start_val_i(current_val_ts1755007826652),
                                                .sum_out_i(inj_sum_out_i_1755007826765_71),
                                                .clk_i(clk)
                                            );
                                            // BEGIN: Module_IfNoneParam_ts1755007826757
                                            assign inj_out_port_1755007826757_895 = temp_int_ts1755007826656;
                                            // END: Module_IfNoneParam_ts1755007826757

                                        assign inj_p2_1755007826750_85_ts1755007826750 = inj_cond1_1755007826640_506_ts1755007826662_ts1755007826750;
                                        // END: child_empty_ports_ts1755007826750

                                        // BEGIN: wide_ops_deep_ts1755007826741
                                        assign inj_wide_out_1755007826741_361 = (((inj_wide_a_1755007826741_677 + inj_wide_b_1755007826741_915) ^ inj_wide_c_1755007826741_137) & (~inj_wide_a_1755007826741_677 | inj_wide_b_1755007826741_915)) + (inj_wide_c_1755007826741_137 >>> 5);
                                        // END: wide_ops_deep_ts1755007826741

                                        MiscExpressions_ValueRange MiscExpressions_ValueRange_inst_1755007826735_1460 (
                                            .out_slice(inj_out_slice_1755007826735_462),
                                            .in_vector(inj_data1_1755007826681_731)
                                        );
                                        // BEGIN: SimpleAssign_ts1755007826728
                                        assign inj_out_data_1755007826728_441 = inj_data_in_1755007826640_804;
                                        // END: SimpleAssign_ts1755007826728

                                    parameter int PARAM_BASIC = 42;
                                    always_ff @(posedge clk) begin
                                        r_state_ts1755007826722 <= ~r_state_ts1755007826722;
                                    end
                                    always_comb begin
                                        inj_o_done_1755007826722_683 = r_state_ts1755007826722;
                                    end
                                    // END: mod_basic_ts1755007826722

                                    Parameterized Parameterized_inst_1755007826714_3092 (
                                        .din(inj_in2_1755007826650_980),
                                        .dout(inj_dout_1755007826714_554)
                                    );
                                    bind_directive_top bind_directive_top_inst_1755007826707_6862 (
                                        .i_control(inj_data2_1755007826665_33),
                                        .i_data(inj_data_in_1755007826640_804),
                                        .o_result(inj_o_result_1755007826707_386),
                                        .o_status(inj_o_status_1755007826707_746),
                                        .i_clk(clk)
                                    );
                                    // BEGIN: ShiftOperations_ts1755007826701
                                    assign inj_left_shift_log_1755007826701_299 = current_val_ts1755007826652 << inj_selector_1755007826642_243;
                                    assign inj_right_shift_log_1755007826701_106 = current_val_ts1755007826652 >> inj_selector_1755007826642_243;
                                    assign inj_right_shift_arith_1755007826701_802 = $signed(current_val_ts1755007826652) >>> inj_selector_1755007826642_243;
                                    // END: ShiftOperations_ts1755007826701

                                    mod_logical_not mod_logical_not_inst_1755007826695_1414 (
                                        .cond_in(unused_line_var_ts1755007826641),
                                        .cond_out(inj_cond_out_1755007826695_846)
                                    );
                                    mod_if_elseif_chained mod_if_elseif_chained_inst_1755007826689_6676 (
                                        .in_value(inj_in1_1755007826640_450),
                                        .out_category(inj_out_category_1755007826689_416)
                                    );
                                    // BEGIN: GenerateIfParam_ts1755007826685
                                    generate
                                        if (GEN) begin : g_true
                                            assign inj_sig_out_1755007826685_658 = inj_cond2_1755007826640_38;
                                        end
                                        else begin : g_false
                                            assign inj_sig_out_1755007826685_658 = ~inj_cond2_1755007826640_38;
                                        end
                                    endgenerate
                                    // END: GenerateIfParam_ts1755007826685

                                    CombinationalLogicExplicit CombinationalLogicExplicit_inst_1755007826681_9549 (
                                        .data_out(inj_data_out_1755007826681_719),
                                        .data0(inj_in_data_1755007826659_929),
                                        .data1(inj_data1_1755007826681_731),
                                        .sel(inj_cond1_1755007826640_506_ts1755007826662)
                                    );
                                block_local_int_ts1755007826677   = internal_sig_b_ts1755007826641 ? 10 : 20;
                                block_local_logic_ts1755007826677 = block_local_int_ts1755007826677;
                                inj_out_c_1755007826677_179             = block_local_logic_ts1755007826677[0];
                            end
                            // END: mod_statement_block_var_ts1755007826677

                        always_comb begin
                            (* full_case *)
                            (* parallel_case *)
                            case (inj_i_sel_1755007826673_383)
                                2'b00: l_temp_ts1755007826673 = inj_i_val_1755007826673_479;
                                2'b01: l_temp_ts1755007826673 = inj_i_val_1755007826673_479 << 1;
                                2'b10: l_temp_ts1755007826673 = inj_i_val_1755007826673_479 >> 1;
                                default: l_temp_ts1755007826673 = 4'bxxxx;
                            endcase
                            (* coverage_off *)
                            begin : my_named_block
                                inj_o_out_1755007826673_983 = l_temp_ts1755007826673;
                            end
                        end
                        // END: mod_case_block_attrs_ts1755007826673

                        // BEGIN: child_module_v1_config_dummy_ts1755007826670
                        assign inj_o_1755007826670_332 = ~inj_cond1_1755007826640_506_ts1755007826662; 
                        // END: child_module_v1_config_dummy_ts1755007826670

                        case_selector case_selector_inst_1755007826665_9148 (
                            .data_out_case(inj_data_out_case_1755007826665_31),
                            .data0(inj_data_in_1755007826649_671),
                            .data1(inj_data1_1755007826665_358),
                            .data2(inj_data2_1755007826665_33),
                            .data3(inj_data3_1755007826665_817),
                            .sel_in(sub_in_ts1755007826656)
                        );
                    assign inj_p2_1755007826662_507_ts1755007826662 = inj_cond1_1755007826640_506_ts1755007826662;
                    // END: child_empty_ports_ts1755007826662

                    StructExample StructExample_inst_1755007826659_5174 (
                        .out_field_a(inj_out_field_a_1755007826659_896),
                        .out_field_b(inj_out_field_b_1755007826659_582),
                        .in_data(inj_in_data_1755007826659_929)
                    );
                ModuleBasic m_inst (
                    .a      (1'b0),
                    .b      (int'(sub_in_ts1755007826656)),
                    .out_a  (),
                    .out_b  (temp_int_ts1755007826656)
                );
                assign inj_data_out_1755007826656_674[i*4 +: 4] = temp_int_ts1755007826656[3:0];
            end
            // END: ModuleHierarchy_High_ts1755007826657

            // BEGIN: BitwiseOperations_ts1755007826654
            assign inj_result_and_1755007826654_433 = inj_data_in_1755007826640_804 & current_val_ts1755007826652;
            assign inj_result_or_1755007826654_514 = inj_data_in_1755007826640_804 | inj_in2_1755007826650_980;
            assign inj_result_xor_1755007826654_693 = current_val_ts1755007826652 ^ inj_in2_1755007826650_980;
            // END: BitwiseOperations_ts1755007826654

        always_comb begin
            current_val_ts1755007826652 = inj_data_in_1755007826649_671;
            for (int k = 0; k < 3; k = k + 1) begin
                current_val_ts1755007826652 = current_val_ts1755007826652 + 1;
            end
            inj_final_val_1755007826652_17 = current_val_ts1755007826652;
        end
        // END: loop_with_internal_assign_ts1755007826652

        // BEGIN: remaining_reduction_ops_ts1755007826650
        assign inj_nand_out_1755007826650_671 = ~&inj_data_in_1755007826640_804;
        assign inj_nor_out_1755007826650_171 = ~|inj_in2_1755007826650_980;
        assign inj_xnor_out_1755007826650_215 = ^~inj_in3_1755007826650_452;
        // END: remaining_reduction_ops_ts1755007826650

        // BEGIN: GenerateFor_ts1755007826649
        genvar i;
        generate
            for (i = 0; i < 4; i = i + 1) begin : g_loop
                assign inj_data_out_1755007826649_494[i] = inj_data_in_1755007826649_671[i];
            end
        endgenerate
        // END: GenerateFor_ts1755007826649

        // BEGIN: ProgramDefinition_ts1755007826647
        assign inj_out_pd_1755007826647_204 = clk;
        // END: ProgramDefinition_ts1755007826647

        // BEGIN: LintLatch_ts1755007826646
        always_comb begin
            if (inj_cond2_1755007826640_38) begin
                inj_out_l_1755007826646_90 = unused_line_var_ts1755007826641;
            end else begin
                inj_out_l_1755007826646_90 = 1'b0; 
            end
        end
        // END: LintLatch_ts1755007826646

        // BEGIN: local_not_allowed_diag_mod_ts1755007826645
        assign inj_out_val_1755007826645_25 = inj_in_val_1755007826645_206;
        // END: local_not_allowed_diag_mod_ts1755007826645

        ModMultipleAlways ModMultipleAlways_inst_1755007826644_9693 (
            .rst_n(reset),
            .dout_a(inj_dout_a_1755007826644_594),
            .dout_b(inj_dout_b_1755007826644_419),
            .clk_a(clk),
            .clk_b(clk),
            .din_a(internal_sig_a_ts1755007826641),
            .din_b(inj_cond1_1755007826640_506)
        );
        configuration_top configuration_top_inst_1755007826643_8579 (
            .i_in(inj_cond1_1755007826640_506),
            .o_out(inj_o_out_1755007826643_816)
        );
        // BEGIN: ModSimpleLogic_ts1755007826643
        assign inj_y_1755007826643_361 = unused_line_var_ts1755007826641 ^ inj_cond1_1755007826640_506;
        // END: ModSimpleLogic_ts1755007826643

        // BEGIN: rand_case_mod_ts1755007826642
        always_comb begin
            case (inj_selector_1755007826642_243)
                0: inj_result_out_1755007826642_811 = 4'h0;
                1: inj_result_out_1755007826642_811 = 4'h1;
                2: inj_result_out_1755007826642_811 = 4'hA;
                default: inj_result_out_1755007826642_811 = 4'hF;
            endcase
        end
        // END: rand_case_mod_ts1755007826642

        module_packed_logic module_packed_logic_inst_1755007826641_2591 (
            .data_in_in_pl(inj_cond1_1755007826640_506),
            .data_in_pl(inj_data_in_pl_1755007826641_476),
            .data_out_pl(inj_data_out_pl_1755007826641_34)
        );
    `line 100 "virtual_file_A.sv" 1
    assign internal_sig_a_ts1755007826641 = inj_cond1_1755007826640_506;
    `line 20 "virtual_file_B.sv" 1
    assign internal_sig_b_ts1755007826641 = ~internal_sig_a_ts1755007826641;
    assign unused_line_var_ts1755007826641 = 1'b1;
    `line 150 "virtual_file_A.sv" 2
    assign inj_out1_1755007826641_16 = internal_sig_b_ts1755007826641;
    `line 1 "original_file.sv" 0
    // END: ModuleLineDirective_ts1755007826641

    mod_split_nested mod_split_nested_inst_1755007826640_3675 (
        .data_in(inj_data_in_1755007826640_804),
        .reset(reset),
        .out_nested_a(inj_out_nested_a_1755007826640_146),
        .out_nested_b(inj_out_nested_b_1755007826640_596),
        .clk(clk),
        .cond1(inj_cond1_1755007826640_506),
        .cond2(inj_cond2_1755007826640_38)
    );
    always @* begin
        inj_out1_1755007826640_377 = inj_in1_1755007826640_450 & inj_in2_1755007826640_656;
        inj_out2_1755007826640_978 = inj_in1_1755007826640_450 | inj_in2_1755007826640_656;
    end
    // END: comb_simple_ts1755007826640
endmodule

