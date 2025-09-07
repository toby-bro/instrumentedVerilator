interface cond_if;
    logic [15:0] control_reg;
    logic [15:0] status_reg;
    modport CtrlStat (output control_reg, input status_reg);
endinterface
interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module HandleOutOfBoundsRead (
    input logic [3:0] i_addr_arr,
    input logic [3:0] i_addr_sel,
    input logic [7:0] i_vector,
    output logic [7:0] o_array_var_elem,
    output logic o_sel_var_bit
);
    parameter ARR_SIZE = 4;
    logic [7:0] my_array [0:ARR_SIZE-1];
    assign my_array[0] = 8'd10;
    assign my_array[1] = 8'd20;
    assign my_array[2] = 8'd30;
    assign my_array[3] = 8'd40;
    assign o_sel_var_bit = i_vector[i_addr_sel];
    assign o_array_var_elem = my_array[i_addr_arr];
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

module bitwise_ops (
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [7:0] in3,
    output logic [7:0] out
);
    assign out = (in1 & in2) | (~in3) ^ (in1 << 2) >> 1;
endmodule

module func_macro_args (
    input int input_int,
    output int output_int
);
    `define ADD(a, b)       ((a) + (b))
    `define SUBTRACT(x, y)  ((x) - (y))
    localparam int P1_ADD = `ADD(10, 20);
    int p2_sub_var;
    always_comb begin
        p2_sub_var = `SUBTRACT(50, input_int);
    end
    assign output_int = P1_ADD + p2_sub_var;
endmodule

module mod_basic_bind (
    input logic in1_bind_def,
    output logic out1_bind_def
);
    assign out1_bind_def = ~in1_bind_def;
endmodule

module mod_sub (
    input wire in_sub,
    output logic out_sub
);
    assign out_sub = in_sub;
endmodule

module module_conditional_write (
    input logic condition,
    input logic [15:0] data_in,
    output logic control_status
);
    cond_if cif_inst();
    always_comb begin
        if (condition) begin
            cif_inst.control_reg = data_in;
        end else begin
            cif_inst.control_reg = 16'h0;
        end
        control_status = (cif_inst.control_reg != 16'h0);
    end
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module simple_assign (
    input logic [7:0] in,
    output logic [7:0] out
);
    assign out = in;
endmodule

module split_if_empty_then (
    input logic clk_p,
    input logic condition_p,
    input logic [7:0] in_val_p,
    output logic [7:0] out_reg_p
);
    always @(posedge clk_p) begin
        if (condition_p) begin
        end else begin
            out_reg_p <= in_val_p;
        end
    end
endmodule

module snippet #(
    parameter int WIDTH = 8
) (
    input wire clk,
    input logic inj_a_1755004216731_406,
    input logic inj_b_1755004216731_819,
    input bit inj_cfg_in_1755004216744_990,
    input logic inj_data0_1755004216732_867,
    input logic [3:0] inj_data_in_1755004216732_208,
    input logic [9:0] inj_data_in_pl_1755004216731_442,
    input logic [7:0] inj_din_1755004216731_295,
    input logic [15:0] inj_in1_1755004216778_837,
    input logic [15:0] inj_in2_1755004216778_825,
    input logic [15:0] inj_in3_1755004216778_894,
    input logic [15:0] inj_in5_1755004216778_896,
    input logic [31:0] inj_in_1755004216732_219,
    input bit [2:0] inj_in_state_case_1755004216736_19,
    input int inj_in_val_1755004216732_736,
    input wire reset,
    output logic [7:0] inj_byte_out_1755004216734_504,
    output bit inj_cfg_out_1755004216744_598,
    output logic inj_control_status_1755004216772_349,
    output logic [7:0] inj_data_a_out_task_1755004216756_10,
    output logic [7:0] inj_data_b_out_task_1755004216756_5,
    output logic [3:0] inj_data_out_1755004216732_756,
    output logic [7:0] inj_data_out_1755004216795_989,
    output logic [4:0] inj_data_out_pl_1755004216731_360,
    output logic [7:0] inj_dout_1755004216731_335,
    output logic inj_keyword_out_1755004216731_321,
    output logic [7:0] inj_o_array_var_elem_1755004216735_216,
    output wire inj_o_c_1755004216742_618,
    output logic inj_o_sel_var_bit_1755004216735_451,
    output logic [7:0] inj_out1_1755004216732_549,
    output logic [7:0] inj_out1_1755004216767_506,
    output logic inj_out1_bind_def_1755004216752_548,
    output logic inj_out2_1755004216732_154,
    output logic inj_out2_1755004216767_434,
    output logic [7:0] inj_out_1755004216745_224,
    output logic inj_out_1755004216778_9,
    output logic [7:0] inj_out_1755004216807_635,
    output logic inj_out_a_1755004216738_993,
    output int inj_out_b_1755004216738_91,
    output logic inj_out_data_q_1755004216739_942,
    output logic inj_out_h_1755004216791_37,
    output logic inj_out_md_1755004216732_357,
    output bit inj_out_priority_case_1755004216736_376,
    output logic [7:0] inj_out_reg_a_1755004216733_232,
    output logic [7:0] inj_out_reg_b_1755004216733_974,
    output logic [7:0] inj_out_reg_p_1755004216740_849,
    output logic [7:0] inj_out_slice_be_1755004216803_359,
    output logic [7:0] inj_out_slice_le_1755004216803_582,
    output logic inj_out_sub_1755004216799_720,
    output bit inj_out_unique_case_1755004216736_538,
    output int inj_out_val_1755004216732_261,
    output int inj_out_val_1755004216784_128,
    output int inj_output_int_1755004216734_379,
    output logic [15:0] inj_packed_out_1755004216734_543,
    output logic inj_result_1755004216732_167,
    output logic inj_sum_1755004216731_908,
    output bit inj_system_status_clear_1755004216747_861,
    output logic inj_task_out_1755004216762_596
);
    // BEGIN: Parameterized_ts1755004216731
    // BEGIN: module_packed_logic_ts1755004216731
    logic [15:0] my_packed_logic_ts1755004216731 ;
        // BEGIN: sequential_logic_ts1755004216733
        ;
        logic [3:0] internal_reg_ts1755004216733;
            // BEGIN: mod_split_ff_ts1755004216733
            logic [7:0]  split_reg_var_ts1755004216733;
            logic [7:0] other_reg_var_ts1755004216733;
                // BEGIN: module_assign_nonblocking_ts1755004216739
                my_if vif_inst();
                logic [7:0] data_q_ts1755004216739;
                    // BEGIN: module_simple_ts1755004216742
                    wire internal_xor_res_ts1755004216742;
                        // BEGIN: module_task_args_ts1755004216757
                        logic [7:0] data_a_ts1755004216757 ;
                        logic [7:0] data_b_ts1755004216757 ;
                            simple_assign simple_assign_inst_1755004216807_8300 (
                                .in(split_reg_var_ts1755004216733),
                                .out(inj_out_1755004216807_635)
                            );
                            // BEGIN: range_select_simple_packed_ts1755004216803
                            assign inj_out_slice_be_1755004216803_359 = inj_in1_1755004216778_837[7:0]; 
                            assign inj_out_slice_le_1755004216803_582 = inj_in1_1755004216778_837[7:0]; 
                            // END: range_select_simple_packed_ts1755004216803

                            mod_sub mod_sub_inst_1755004216799_1531 (
                                .out_sub(inj_out_sub_1755004216799_720),
                                .in_sub(internal_xor_res_ts1755004216742)
                            );
                            // BEGIN: sequential_register_en_ts1755004216795
                            always_ff @(posedge clk) begin
                                if (inj_data0_1755004216732_867) begin
                                    inj_data_out_1755004216795_989 <= other_reg_var_ts1755004216733;
                                end
                            end
                            // END: sequential_register_en_ts1755004216795

                            // BEGIN: CoverageHelper_ts1755004216791
                            assign inj_out_h_1755004216791_37 = inj_cfg_in_1755004216744_990;
                            // END: CoverageHelper_ts1755004216791

                            // BEGIN: recursive_param_diag_mod_ts1755004216784
                            assign inj_out_val_1755004216784_128 = inj_in_val_1755004216732_736;
                            // END: recursive_param_diag_mod_ts1755004216784

                            // BEGIN: arith_comp_ops_ts1755004216778
                            assign inj_out_1755004216778_9 = (inj_in1_1755004216778_837 + inj_in2_1755004216778_825) * inj_in3_1755004216778_894 > my_packed_logic_ts1755004216731 - inj_in5_1755004216778_896;
                            // END: arith_comp_ops_ts1755004216778

                            module_conditional_write module_conditional_write_inst_1755004216772_1274 (
                                .control_status(inj_control_status_1755004216772_349),
                                .condition(inj_b_1755004216731_819),
                                .data_in(my_packed_logic_ts1755004216731)
                            );
                            // BEGIN: constant_sel_ts1755004216767
                            assign inj_out1_1755004216767_506 = inj_in_1755004216732_219[15:8];
                            assign inj_out2_1755004216767_434 = inj_in_1755004216732_219[3];
                            // END: constant_sel_ts1755004216767

                            // BEGIN: task_example_ts1755004216762
                            task automatic process_data (input logic data);
                                logic temp_ts1755004216762;
                                temp_ts1755004216762 = data; 
                            endtask 
                            assign inj_task_out_1755004216762_596 = inj_b_1755004216731_819;
                            // END: task_example_ts1755004216762

                        task automatic modify_vars;
                            input logic [7:0] task_arg_ts1755004216757;
                            logic [7:0] task_local_ts1755004216757 ;
                            begin
                                task_local_ts1755004216757 = task_arg_ts1755004216757;
                                data_a_ts1755004216757 = task_local_ts1755004216757 + 8'd1;
                                data_b_ts1755004216757 = task_arg_ts1755004216757 - 8'd1;
                            end
                        endtask
                        always_comb begin
                            if (inj_a_1755004216731_406) begin
                                data_a_ts1755004216757 = other_reg_var_ts1755004216733;
                                data_b_ts1755004216757 = 8'hFF;
                                modify_vars(inj_din_1755004216731_295);
                            end else begin
                                data_a_ts1755004216757 = 8'h00;
                                data_b_ts1755004216757 = 8'h00;
                            end
                        end
                        always_comb begin
                            inj_data_a_out_task_1755004216756_10 = data_a_ts1755004216757 + 8'd2;
                            inj_data_b_out_task_1755004216756_5 = data_b_ts1755004216757;
                        end
                        // END: module_task_args_ts1755004216757

                        mod_basic_bind mod_basic_bind_inst_1755004216752_2991 (
                            .out1_bind_def(inj_out1_bind_def_1755004216752_548),
                            .in1_bind_def(inj_a_1755004216731_406)
                        );
                        // BEGIN: PragmaResetDirectives_ts1755004216748
                    `ifdef SLANG_PRAGMA
                    `reset protect diagnostic
                    `endif
                    assign inj_system_status_clear_1755004216747_861 = reset;
                        // END: PragmaResetDirectives_ts1755004216748

                        bitwise_ops bitwise_ops_inst_1755004216745_1058 (
                            .in1(data_q_ts1755004216739),
                            .in2(inj_din_1755004216731_295),
                            .in3(other_reg_var_ts1755004216733),
                            .out(inj_out_1755004216745_224)
                        );
                        // BEGIN: Module_ConfigKeywords_ts1755004216744
                        assign inj_cfg_out_1755004216744_598 = inj_cfg_in_1755004216744_990;
                        // END: Module_ConfigKeywords_ts1755004216744

                    assign internal_xor_res_ts1755004216742 = clk ^ reset;
                    assign inj_o_c_1755004216742_618 = internal_xor_res_ts1755004216742 & clk;
                    // END: module_simple_ts1755004216742

                    split_if_empty_then split_if_empty_then_inst_1755004216740_7045 (
                        .in_val_p(data_q_ts1755004216739),
                        .out_reg_p(inj_out_reg_p_1755004216740_849),
                        .clk_p(clk),
                        .condition_p(inj_a_1755004216731_406)
                    );
                always_ff @(posedge clk or posedge reset) begin
                    if (reset) begin
                        vif_inst.data <= 8'h0;
                        data_q_ts1755004216739 <= 8'h0;
                    end else begin
                        vif_inst.data <= other_reg_var_ts1755004216733;
                        data_q_ts1755004216739 <= vif_inst.data;
                    end
                end
                assign inj_out_data_q_1755004216739_942 = data_q_ts1755004216739;
                // END: module_assign_nonblocking_ts1755004216739

                ModuleBasic ModuleBasic_inst_1755004216738_2874 (
                    .out_a(inj_out_a_1755004216738_993),
                    .out_b(inj_out_b_1755004216738_91),
                    .a(inj_b_1755004216731_819),
                    .b(inj_in_val_1755004216732_736)
                );
                // BEGIN: mod_case_unique_priority_ts1755004216736
            always_comb begin
                inj_out_unique_case_1755004216736_538 = 1'b0;
                unique case (inj_in_state_case_1755004216736_19)
                    3'd0: inj_out_unique_case_1755004216736_538 = 1'b0;
                    3'd1: inj_out_unique_case_1755004216736_538 = 1'b1;
                    3'd2: inj_out_unique_case_1755004216736_538 = 1'b0;
                    3'd1: inj_out_unique_case_1755004216736_538 = 1'b1;
                    default: inj_out_unique_case_1755004216736_538 = 1'b1;
                endcase
            end
            always_comb begin
                inj_out_priority_case_1755004216736_376 = 1'b0;
                priority case (inj_in_state_case_1755004216736_19)
                    3'd0: inj_out_priority_case_1755004216736_376 = 1'b0;
                    3'd1: inj_out_priority_case_1755004216736_376 = 1'b1;
                    3'd2: inj_out_priority_case_1755004216736_376 = 1'b0;
                    3'd1: inj_out_priority_case_1755004216736_376 = 1'b1;
                    default: inj_out_priority_case_1755004216736_376 = 1'b1;
                endcase
            end
                // END: mod_case_unique_priority_ts1755004216736

                HandleOutOfBoundsRead HandleOutOfBoundsRead_inst_1755004216735_1177 (
                    .i_addr_arr(internal_reg_ts1755004216733),
                    .i_addr_sel(inj_data_in_1755004216732_208),
                    .i_vector(other_reg_var_ts1755004216733),
                    .o_array_var_elem(inj_o_array_var_elem_1755004216735_216),
                    .o_sel_var_bit(inj_o_sel_var_bit_1755004216735_451)
                );
                // BEGIN: PackedStructOps_ts1755004216735
                typedef struct packed {
                    logic [7:0] low_ts1755004216735;
                    logic [7:0] high_ts1755004216735;
                } pair_t;
                pair_t data_pair;
                assign data_pair.high_ts1755004216735 = my_packed_logic_ts1755004216731[15:8];
                assign data_pair.low_ts1755004216735 = split_reg_var_ts1755004216733;
                assign inj_byte_out_1755004216734_504 = data_pair.high_ts1755004216735;
                assign inj_packed_out_1755004216734_543[15:8] = data_pair.high_ts1755004216735;
                assign inj_packed_out_1755004216734_543[7:0] = data_pair.low_ts1755004216735 + split_reg_var_ts1755004216733;
                // END: PackedStructOps_ts1755004216735

                func_macro_args func_macro_args_inst_1755004216734_3852 (
                    .input_int(inj_in_val_1755004216732_736),
                    .output_int(inj_output_int_1755004216734_379)
                );
            always_ff @(posedge clk or posedge reset) begin
                if (reset) begin
                    split_reg_var_ts1755004216733 <= 8'b0;
                    other_reg_var_ts1755004216733 <= 8'b0;
                    inj_out_reg_a_1755004216733_232 <= 8'b0;
                    inj_out_reg_b_1755004216733_974 <= 8'b0;
                end else begin
                    split_reg_var_ts1755004216733 <= inj_din_1755004216731_295;
                    other_reg_var_ts1755004216733 <= inj_din_1755004216731_295 + 2;
                    inj_out_reg_a_1755004216733_232 <= split_reg_var_ts1755004216733;
                    inj_out_reg_b_1755004216733_974 <= other_reg_var_ts1755004216733;
                end
            end
            // END: mod_split_ff_ts1755004216733

        always_ff @(posedge clk or negedge reset) begin
            if (!reset) begin
                internal_reg_ts1755004216733 <= 4'h0;
            end else begin
                internal_reg_ts1755004216733 <= inj_data_in_1755004216732_208;
            end
        end
        assign inj_data_out_1755004216732_756 = internal_reg_ts1755004216733;
        // END: sequential_logic_ts1755004216733

        // BEGIN: constant_sel_ts1755004216732
        assign inj_out1_1755004216732_549 = inj_in_1755004216732_219[15:8];
        assign inj_out2_1755004216732_154 = inj_in_1755004216732_219[3];
        // END: constant_sel_ts1755004216732

        // BEGIN: module_in_program_ref_ts1755004216732
        assign inj_out_val_1755004216732_261 = inj_in_val_1755004216732_736;
        // END: module_in_program_ref_ts1755004216732

        // BEGIN: multiplexer_2to1_ts1755004216732
        assign inj_result_1755004216732_167 = inj_b_1755004216731_819 ? inj_a_1755004216731_406 : inj_data0_1755004216732_867;
        // END: multiplexer_2to1_ts1755004216732

        // BEGIN: ModuleDefinition_ts1755004216732
        assign inj_out_md_1755004216732_357 = clk;
        // END: ModuleDefinition_ts1755004216732

        // BEGIN: keyword_import_export_ts1755004216731
        assign inj_keyword_out_1755004216731_321 = inj_a_1755004216731_406;
        // END: keyword_import_export_ts1755004216731

    always_comb begin
        my_packed_logic_ts1755004216731[9:0] = inj_data_in_pl_1755004216731_442;
        my_packed_logic_ts1755004216731[15:10] = 6'h3F;
        my_packed_logic_ts1755004216731[0] = inj_a_1755004216731_406;
    end
    assign inj_data_out_pl_1755004216731_360[4:1] = my_packed_logic_ts1755004216731[4:1];
    assign inj_data_out_pl_1755004216731_360[0] = my_packed_logic_ts1755004216731[1];
    // END: module_packed_logic_ts1755004216731

    assign inj_dout_1755004216731_335 = inj_din_1755004216731_295;
    // END: Parameterized_ts1755004216731

    simple_adder simple_adder_inst_1755004216731_1152 (
        .a(inj_a_1755004216731_406),
        .b(inj_b_1755004216731_819),
        .sum(inj_sum_1755004216731_908)
    );
endmodule

