interface cond_if;
    logic [15:0] control_reg;
    logic [15:0] status_reg;
    modport CtrlStat (output control_reg, input status_reg);
endinterface
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

module FunctionTaskMod (
    input logic [7:0] data_in,
    output logic is_even
);
    function automatic bit check_even(input logic [7:0] v);
        check_even = ~v[0];
    endfunction
    task automatic dummy_task(input logic [7:0] v);
        int tmp;
        tmp = v;
    endtask
    assign is_even = check_even(data_in);
endmodule

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

module LintSensitiveList (
    input logic in_p,
    input logic in_q,
    output logic out_r
);
    always_comb begin
        out_r = in_p | in_q;
    end
endmodule

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

module ModWideBus (
    input logic [31:0] data_in_w,
    output logic [31:0] data_out_w
);
    assign data_out_w = ~data_in_w;
endmodule

module always_comb_if (
    input logic cond,
    input logic [31:0] in1,
    input logic [31:0] in2,
    output logic [31:0] out
);
    always_comb begin
        if (cond) begin
            out = in1;
        end else begin
            out = in2;
        end
    end
endmodule

module basic_d_flipflop (
    input logic clk,
    input logic d,
    output logic q
);
    always_ff @(posedge clk) begin
        q <= d;
    end
endmodule

module case_full_parallel_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        (* full, parallel *)
        case (case_expr)
            2'b00: internal_out = 1;
            2'b01: internal_out = 2;
            2'b10: internal_out = 3;
            default: internal_out = 4;
        endcase
    end
endmodule

module coalesced_assign (
    input logic [3:0] in_h,
    input logic [3:0] in_l,
    output logic [7:0] out
);
    wire [7:0] temp_wire;
    assign temp_wire[7:4] = in_h;
    assign temp_wire[3:0] = in_l;
    assign out = temp_wire;
endmodule

module comb_conditional (
    input bit [7:0] data1,
    input bit [7:0] data2,
    input bit sel,
    output bit [7:0] result1,
    output bit [7:0] result2
);
    always @* begin
        if (sel) begin
            result1 = data1;
            result2 = data1;
        end else begin
            result1 = data2;
            result2 = data2;
        end
    end
endmodule

module definition_used_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module mod_seq_reg (
    input logic clk,
    input logic d,
    output logic q
);
    always_ff @(posedge clk) begin
        q <= d;
    end
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

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
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

module split_reorder_blocking (
    input logic [7:0] in_a_g,
    input logic [7:0] in_b_g,
    output logic [7:0] out_p_g,
    output logic [7:0] out_q_g
);
    logic [7:0] mid_x_g;
    logic [7:0] mid_y_g;
    always @(*) begin
        mid_x_g = in_a_g * 2;
        mid_y_g = mid_x_g + in_b_g;
        out_p_g = mid_y_g - 1;
        out_q_g = mid_x_g / 2;
    end
endmodule

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module task_example (
    input logic task_in,
    output logic task_out
);
    task automatic process_data (input logic data);
        logic temp;
        temp = data; 
    endtask 
    assign task_out = task_in;
endmodule

module udnt_port_module (
    input logic udnt_input,
    input logic uin,
    output logic udnt_output,
    output logic uout
);
    assign uout = uin;
    assign udnt_output = udnt_input;
endmodule

module snippet #(
    parameter int P_PORT_VAL = 25,
    parameter int WIDTH = 8
) (
    input wire clk,
    input logic inj_concat_port_input_1755007847524_445,
    input logic [15:0] inj_data0_1755007847530_108,
    input bit [7:0] inj_data1_1755007847660_172,
    input bit [7:0] inj_data2_1755007847660_338,
    input logic [7:0] inj_data_in_1755007847526_883,
    input logic [15:0] inj_data_in_1755007847528_275,
    input wire [3:0] inj_in0_1755007847538_158,
    input wire [3:0] inj_in1_1755007847538_641,
    input bit [3:0] inj_in1_1755007847672_278,
    input logic [31:0] inj_in1_1755007847765_126,
    input wire [3:0] inj_in2_1755007847538_106,
    input bit [3:0] inj_in2_1755007847672_279,
    input logic [31:0] inj_in2_1755007847765_91,
    input wire [3:0] inj_in3_1755007847538_104,
    input wire [7:0] inj_in_a_1755007847643_773,
    input wire [7:0] inj_in_c_1755007847643_614,
    input wire [7:0] inj_in_const1_1755007847643_201,
    input wire [7:0] inj_in_const2_1755007847643_639,
    input logic [3:0] inj_in_h_1755007847536_613,
    input wire [2:0] inj_in_index_1755007847524_697,
    input logic [3:0] inj_in_l_1755007847536_16,
    input wire [7:0] inj_in_latch_data_1755007847524_625,
    input wire [1:0] inj_in_part_lsb_1755007847524_519,
    input logic [2:0] inj_in_shift_1755007847573_883,
    input int inj_in_val_1755007847754_550,
    input bit inj_sel_1755007847660_801,
    input logic [4:0] inj_start_bit_1755007848164_921,
    input wire reset,
    output logic inj_and_reduce_1755007847712_210,
    output logic inj_bit_out_1755007848164_528,
    output logic [7:0] inj_byte_out_1755007848164_508,
    output logic inj_concat_port_output_1755007847524_784,
    output logic inj_control_status_1755007847528_626,
    output wire [2:0] inj_count_out_1755007848275_242,
    output logic inj_data_out_1755007847525_371,
    output logic [15:0] inj_data_out_1755007847530_643,
    output logic [31:0] inj_data_out_w_1755007848035_816,
    output logic [7:0] inj_field0_byte_o_1755007847626_525,
    output logic [7:0] inj_final_val_1755007847545_733,
    output logic inj_fs_out_target_1755007847579_714,
    output logic [4:0] inj_internal_out_1755007847634_263,
    output logic [4:0] inj_internal_out_1755007847900_986,
    output logic inj_is_even_1755007847549_598,
    output reg [3:0] inj_mux_out_1755007847538_923,
    output logic inj_named_out_1755007848060_448,
    output reg inj_non_ansi_b_1755007847740_165,
    output logic inj_non_ansi_basic_output_1755007847740_316,
    output logic [1:0] inj_non_ansi_i_1755007847524_50,
    output logic [1:0] inj_non_ansi_j_1755007847524_155,
    output wire inj_o_1755007847727_115,
    output logic inj_o_1755007848085_789,
    output logic [7:0] inj_o_array_var_elem_1755007847591_325,
    output logic inj_o_bind_status_1755007847543_205,
    output wire inj_o_c_1755007847685_828,
    output logic inj_o_done_1755007847558_326,
    output logic [7:0] inj_o_out_1755007847527_9,
    output logic inj_o_out_1755007847921_553,
    output logic inj_o_sel_var_bit_1755007847591_899,
    output logic [7:0] inj_o_sum_1755007847532_690,
    output logic [7:0] inj_o_target_result_1755007847552_112,
    output logic [7:0] inj_o_target_result_1755007847612_15,
    output logic inj_or_reduce_1755007847712_636,
    output logic [15:0] inj_out1_1755007847562_209,
    output logic [7:0] inj_out1_1755007847618_488,
    output bit [3:0] inj_out1_1755007847672_732,
    output logic [7:0] inj_out1_1755007847987_803,
    output logic [7:0] inj_out1_z_1755007847605_767,
    output logic [15:0] inj_out2_1755007847562_639,
    output bit [3:0] inj_out2_1755007847672_118,
    output logic [7:0] inj_out2_1755007847987_479,
    output logic [7:0] inj_out2_z_1755007847605_820,
    output logic [7:0] inj_out_1755007847536_443,
    output logic [3:0] inj_out_1755007847585_55,
    output logic [31:0] inj_out_1755007847765_528,
    output logic [7:0] inj_out_1755007848247_814,
    output logic [7:0] inj_out_a_1755007847526_576,
    output logic [7:0] inj_out_add_assoc_1755007847643_757,
    output logic [7:0] inj_out_and_assoc_1755007847643_831,
    output logic [7:0] inj_out_and_swap_const_1755007847643_250,
    output logic [7:0] inj_out_arith_1755007847643_532,
    output logic [7:0] inj_out_b_1755007847526_739,
    output logic inj_out_bit_select_1755007847524_962,
    output logic inj_out_bit_select_1755007847809_815,
    output logic [7:0] inj_out_bitwise_1755007847643_189,
    output logic [7:0] inj_out_bitwise_ops_1755007847524_732,
    output logic [7:0] inj_out_bitwise_ops_1755007847809_204,
    output logic inj_out_cmp_1755007847880_339,
    output wire [3:0] inj_out_element_1755007848111_42,
    output logic [7:0] inj_out_func_result_1755007847775_455,
    output reg [7:0] inj_out_latch_reg_1755007847524_37,
    output logic inj_out_logic_1755007848138_549,
    output logic inj_out_logical_1755007847643_616,
    output logic [7:0] inj_out_mul_assoc_1755007847643_642,
    output logic [7:0] inj_out_negate_1755007847643_525,
    output logic [7:0] inj_out_ops_1755007847880_635,
    output logic [7:0] inj_out_or_assoc_1755007847643_623,
    output logic [7:0] inj_out_or_swap_not_1755007847643_351,
    output logic [7:0] inj_out_p_g_1755007848012_109,
    output logic [3:0] inj_out_part_1755007847573_351,
    output logic [3:0] inj_out_part_select_1755007847524_933,
    output logic [3:0] inj_out_part_select_1755007847809_122,
    output logic [7:0] inj_out_q_1755007847943_461,
    output logic [7:0] inj_out_q_g_1755007848012_539,
    output logic inj_out_r_1755007847555_664,
    output logic inj_out_r_1755007847792_233,
    output logic inj_out_r_1755007847841_181,
    output logic [7:0] inj_out_reg_1755007847573_201,
    output reg inj_out_res_1755007847597_500,
    output reg inj_out_res_1755007847964_49,
    output reg inj_out_res_1755007848218_852,
    output bit [3:0] inj_out_result_1755007847823_485,
    output logic inj_out_single_1755007847567_630,
    output logic [7:0] inj_out_unary_not_1755007847643_181,
    output int inj_out_val_1755007847754_80,
    output logic [7:0] inj_out_vector_assign_1755007847524_942,
    output logic [7:0] inj_out_vector_assign_1755007847809_364,
    output logic inj_out_wire_1755007848192_545,
    output logic [7:0] inj_out_xor_assoc_1755007847643_495,
    output logic [7:0] inj_out_xor_swap_var_1755007847643_505,
    output logic inj_q_1755007847525_747,
    output logic inj_q_1755007847534_146,
    output bit [7:0] inj_result1_1755007847660_384,
    output bit [7:0] inj_result2_1755007847660_742,
    output logic inj_task_out_1755007847860_874,
    output logic inj_tok_out_1755007847815_945,
    output logic inj_udnt_output_1755007847699_685,
    output logic inj_uout_1755007847699_624,
    output logic inj_xor_reduce_1755007847712_897
);
    // BEGIN: module_latch_ts1755007847524
    // BEGIN: non_ansi_concat_port_ts1755007847524
    output logic [1:0] inj_non_ansi_i_1755007847524_50_ts1755007847524;
    output logic [1:0] inj_non_ansi_j_1755007847524_155_ts1755007847524;
    input logic inj_concat_port_input_1755007847524_445_ts1755007847524;
    output logic inj_concat_port_output_1755007847524_784_ts1755007847524;
        // BEGIN: mod_split_comb_ts1755007847526
        logic [7:0]  split_comb_var_ts1755007847526;
        logic [7:0] other_comb_var_ts1755007847526;
            // BEGIN: mod_module_attrs_ts1755007847527
            logic [WIDTH-1:0] r_data_ts1755007847527;
                // BEGIN: loop_with_internal_assign_ts1755007847546
                logic [7:0] current_val_ts1755007847546;
                    // BEGIN: mod_basic_ts1755007847558
                    logic r_state_ts1755007847558;
                        // BEGIN: procedural_complex_ts1755007847562
                        logic [15:0] temp1_ts1755007847562;
                        logic [15:0] temp2_ts1755007847562;
                            // BEGIN: module_assignments_in_loops_ts1755007847574
                            localparam int PART_START = 4;
                            localparam int PART_WIDTH = 4;
                            logic [7:0] reg_var_ts1755007847573;
                            logic [3:0] part_var_ts1755007847573;
                                // BEGIN: basic_comb_ts1755007847619
                                ;
                                logic [7:0] temp_wire_ts1755007847619;
                                    // BEGIN: Mod_BasicOps_ts1755007847650
                                    logic [7:0] intermediate_arith_ts1755007847647;
                                    logic [7:0] intermediate_bitwise_ts1755007847647;
                                    logic [0:0] intermediate_logical_ts1755007847647;
                                    logic [7:0] intermediate_add_assoc_ts1755007847647;
                                    logic [7:0] intermediate_mul_assoc_ts1755007847647;
                                    logic [7:0] intermediate_and_assoc_ts1755007847647;
                                    logic [7:0] intermediate_or_assoc_ts1755007847647;
                                    logic [7:0] intermediate_xor_assoc_ts1755007847647;
                                        // BEGIN: ModuleFF_ts1755007847673
                                        parameter int MAX_COUNT = 10;
                                        localparam int START_VAL = 5;
                                        logic [3:0] ff_reg_ts1755007847673;
                                        integer unused_int_var_ts1755007847673;
                                            // BEGIN: module_simple_ts1755007847686
                                            wire internal_xor_res_ts1755007847686;
                                                // BEGIN: non_ansi_basic_ts1755007847740
                                                input wire reset_ts1755007847740;
                                                output reg inj_non_ansi_b_1755007847740_165_ts1755007847740;
                                                input logic inj_concat_port_input_1755007847524_445_ts1755007847740;
                                                output logic inj_non_ansi_basic_output_1755007847740_316_ts1755007847740;
                                                    // BEGIN: module_function_ts1755007847776
                                                    function automatic [7:0] add_and_subtract;
                                                    input [7:0] val1;
                                                    input [7:0] val2;
                                                    reg [7:0] temp_ts1755007847776;
                                                        // BEGIN: Module_BasicSyntax_ts1755007847881
                                                        logic [7:0] temp_ts1755007847881;
                                                            // BEGIN: attributes_on_expr_port_ts1755007847921
                                                            logic internal_sig_ts1755007847921;
                                                                // BEGIN: ModuleComb_ts1755007847988
                                                                logic [7:0] internal_wire_ts1755007847988;
                                                                    // BEGIN: module_with_param_ts1755007848060
                                                                    parameter int DELAY = 10;
                                                                    logic bind_dummy_in_ts1755007848060;
                                                                    logic bind_dummy_out_ts1755007848060;
                                                                        // BEGIN: unpacked_array_module_ts1755007848111
                                                                        logic [3:0] data_array_ts1755007848111 [4];
                                                                            // BEGIN: simple_seq_ts1755007848276
                                                                            reg [2:0] counter_reg_ts1755007848276;
                                                                            always @(posedge clk or posedge reset) begin
                                                                                if (reset) begin
                                                                                    counter_reg_ts1755007848276 <= 3'b000;
                                                                                end else begin
                                                                                    counter_reg_ts1755007848276 <= inj_in_index_1755007847524_697 + 3'b001;
                                                                                end
                                                                            end
                                                                            assign inj_count_out_1755007848275_242 = counter_reg_ts1755007848276;
                                                                            // END: simple_seq_ts1755007848276

                                                                            // BEGIN: deep_logic_ts1755007848247
                                                                            assign inj_out_1755007848247_814 = (((inj_data_in_1755007847526_883 & intermediate_add_assoc_ts1755007847647) | (~intermediate_arith_ts1755007847647)) ^ (inj_data_in_1755007847526_883 + intermediate_add_assoc_ts1755007847647)) - (intermediate_arith_ts1755007847647 << 2);
                                                                            // END: deep_logic_ts1755007848247

                                                                            // BEGIN: case_default_ts1755007848218
                                                                            always_comb begin
                                                                                inj_out_res_1755007848218_852 = 1'b0;
                                                                                case (inj_non_ansi_j_1755007847524_155_ts1755007847524)
                                                                                    2'b01: inj_out_res_1755007848218_852 = 1'b1;
                                                                                    2'b10: inj_out_res_1755007848218_852 = 1'b0;
                                                                                    default: inj_out_res_1755007848218_852 = 1'b1;
                                                                                endcase
                                                                            end
                                                                            // END: case_default_ts1755007848218

                                                                            // BEGIN: net_var_conn_child_ts1755007848192
                                                                            assign inj_out_wire_1755007848192_545 = inj_concat_port_input_1755007847524_445_ts1755007847524;
                                                                            // END: net_var_conn_child_ts1755007848192

                                                                            ArrayIndexAndPartSelect ArrayIndexAndPartSelect_inst_1755007848164_6526 (
                                                                                .start_bit(inj_start_bit_1755007848164_921),
                                                                                .bit_out(inj_bit_out_1755007848164_528),
                                                                                .byte_out(inj_byte_out_1755007848164_508),
                                                                                .data_in(inj_in1_1755007847765_126),
                                                                                .index_in(inj_in_val_1755007847754_550)
                                                                            );
                                                                            // BEGIN: DummyHierModule_ts1755007848138
                                                                            assign inj_out_logic_1755007848138_549 = inj_sel_1755007847660_801;
                                                                            // END: DummyHierModule_ts1755007848138

                                                                        always @(*) begin
                                                                            data_array_ts1755007848111[0] = inj_in_a_1755007847643_773[3:0];
                                                                            data_array_ts1755007848111[1] = inj_in_a_1755007847643_773[7:4];
                                                                            data_array_ts1755007848111[2] = 4'd8;
                                                                            data_array_ts1755007848111[3] = 4'd12;
                                                                        end
                                                                        assign inj_out_element_1755007848111_42 = data_array_ts1755007848111[inj_in_part_lsb_1755007847524_519];
                                                                        // END: unpacked_array_module_ts1755007848111

                                                                        // BEGIN: child_module_v1_config_dummy_ts1755007848085
                                                                        assign inj_o_1755007848085_789 = ~internal_sig_ts1755007847921; 
                                                                        // END: child_module_v1_config_dummy_ts1755007848085

                                                                    assign inj_named_out_1755007848060_448 = inj_concat_port_input_1755007847524_445_ts1755007847740;
                                                                    // END: module_with_param_ts1755007848060

                                                                    ModWideBus ModWideBus_inst_1755007848035_4608 (
                                                                        .data_out_w(inj_data_out_w_1755007848035_816),
                                                                        .data_in_w(inj_in1_1755007847765_126)
                                                                    );
                                                                    split_reorder_blocking split_reorder_blocking_inst_1755007848012_8185 (
                                                                        .in_a_g(intermediate_xor_assoc_ts1755007847647),
                                                                        .in_b_g(intermediate_mul_assoc_ts1755007847647),
                                                                        .out_p_g(inj_out_p_g_1755007848012_109),
                                                                        .out_q_g(inj_out_q_g_1755007848012_539)
                                                                    );
                                                                assign internal_wire_ts1755007847988 = intermediate_and_assoc_ts1755007847647 + intermediate_bitwise_ts1755007847647;
                                                                always_comb begin
                                                                    if (internal_wire_ts1755007847988 > 8'd128) begin
                                                                        inj_out1_1755007847987_803 = internal_wire_ts1755007847988 - 1;
                                                                    end else begin
                                                                        inj_out1_1755007847987_803 = internal_wire_ts1755007847988 + 1;
                                                                    end
                                                                    inj_out2_1755007847987_479 = internal_wire_ts1755007847988 / 2;
                                                                end
                                                                // END: ModuleComb_ts1755007847988

                                                                // BEGIN: case_empty_statement_ts1755007847964
                                                                always_comb begin
                                                                    inj_out_res_1755007847964_49 = 1'b0;
                                                                    case (inj_non_ansi_j_1755007847524_155_ts1755007847524)
                                                                        2'b00: inj_out_res_1755007847964_49 = 1'b1;
                                                                        2'b01: ;
                                                                        2'b10: inj_out_res_1755007847964_49 = 1'b0;
                                                                        default: inj_out_res_1755007847964_49 = 1'b1;
                                                                    endcase
                                                                end
                                                                // END: case_empty_statement_ts1755007847964

                                                                // BEGIN: split_single_stmt_ts1755007847943
                                                                always @(*) begin
                                                                    inj_out_q_1755007847943_461 = intermediate_xor_assoc_ts1755007847647 + 1;
                                                                end
                                                                // END: split_single_stmt_ts1755007847943

                                                            assign internal_sig_ts1755007847921 = inj_concat_port_output_1755007847524_784_ts1755007847524 & inj_non_ansi_basic_output_1755007847740_316_ts1755007847740;
                                                            simple_adder sa_inst(
                                                                .a  (inj_concat_port_output_1755007847524_784_ts1755007847524),
                                                                (* fanout_limit = 10 *) .b(inj_non_ansi_basic_output_1755007847740_316_ts1755007847740),
                                                                .sum(inj_o_out_1755007847921_553)
                                                            );
                                                            // END: attributes_on_expr_port_ts1755007847921

                                                            // BEGIN: case_full_parallel_mod_ts1755007847900
                                                            always @* begin
                                                                (* full, parallel *)
                                                                case (inj_non_ansi_i_1755007847524_50_ts1755007847524)
                                                                    2'b00: inj_internal_out_1755007847900_986 = 1;
                                                                    2'b01: inj_internal_out_1755007847900_986 = 2;
                                                                    2'b10: inj_internal_out_1755007847900_986 = 3;
                                                                    default: inj_internal_out_1755007847900_986 = 4;
                                                                endcase
                                                            end
                                                            // END: case_full_parallel_mod_ts1755007847900

                                                        always_comb begin
                                                            temp_ts1755007847881 = intermediate_add_assoc_ts1755007847647 + inj_data_in_1755007847526_883;
                                                        end
                                                        assign inj_out_ops_1755007847880_635 = (intermediate_add_assoc_ts1755007847647 & inj_data_in_1755007847526_883) | (intermediate_add_assoc_ts1755007847647 ^ inj_data_in_1755007847526_883);
                                                        assign inj_out_cmp_1755007847880_339 = (intermediate_add_assoc_ts1755007847647 == inj_data_in_1755007847526_883);
                                                        // END: Module_BasicSyntax_ts1755007847881

                                                        task_example task_example_inst_1755007847860_892 (
                                                            .task_in(r_state_ts1755007847558),
                                                            .task_out(inj_task_out_1755007847860_874)
                                                        );
                                                        // BEGIN: LintSensitiveList_ts1755007847841
                                                        always_comb begin
                                                            inj_out_r_1755007847841_181 = inj_concat_port_output_1755007847524_784_ts1755007847524 | inj_concat_port_input_1755007847524_445;
                                                        end
                                                        // END: LintSensitiveList_ts1755007847841

                                                        // BEGIN: mod_if_else_simple_ts1755007847823
                                                    always_comb begin
                                                        if (inj_in2_1755007847672_279 > 8) begin
                                                            inj_out_result_1755007847823_485 = inj_in2_1755007847672_279 + 1;
                                                        end else begin
                                                            inj_out_result_1755007847823_485 = inj_in2_1755007847672_279 - 1;
                                                        end
                                                    end
                                                        // END: mod_if_else_simple_ts1755007847823

                                                        // BEGIN: Module_MacroTokens_ts1755007847815
                                                        `define PASTE(a,b) a``b
                                                        logic `PASTE(my,_var);
                                                        always_comb begin
                                                            `PASTE(my,_var) = inj_concat_port_input_1755007847524_445;
                                                            inj_tok_out_1755007847815_945         = `PASTE(my,_var);
                                                        end
                                                        // END: Module_MacroTokens_ts1755007847815

                                                        module_selection module_selection_inst_1755007847809_1511 (
                                                            .in_vector(inj_in_c_1755007847643_614),
                                                            .out_bit_select(inj_out_bit_select_1755007847809_815),
                                                            .out_bitwise_ops(inj_out_bitwise_ops_1755007847809_204),
                                                            .out_part_select(inj_out_part_select_1755007847809_122),
                                                            .out_vector_assign(inj_out_vector_assign_1755007847809_364),
                                                            .in_bit(clk),
                                                            .in_index(inj_in_index_1755007847524_697),
                                                            .in_part_lsb(inj_in_part_lsb_1755007847524_519)
                                                        );
                                                        // BEGIN: LintSensitiveList_ts1755007847792
                                                        always_comb begin
                                                            inj_out_r_1755007847792_233 = r_state_ts1755007847558 | inj_concat_port_output_1755007847524_784_ts1755007847524;
                                                        end
                                                        // END: LintSensitiveList_ts1755007847792

                                                    begin
                                                    temp_ts1755007847776 = val1 + val2;
                                                    add_and_subtract = temp_ts1755007847776 - 1;
                                                    end
                                                    endfunction
                                                    always_comb begin
                                                    inj_out_func_result_1755007847775_455 = add_and_subtract(inj_in_latch_data_1755007847524_625, inj_in_const2_1755007847643_639);
                                                    end
                                                    // END: module_function_ts1755007847776

                                                    always_comb_if always_comb_if_inst_1755007847765_8636 (
                                                        .in1(inj_in1_1755007847765_126),
                                                        .in2(inj_in2_1755007847765_91),
                                                        .out(inj_out_1755007847765_528),
                                                        .cond(inj_non_ansi_basic_output_1755007847740_316_ts1755007847740)
                                                    );
                                                    definition_used_diag_mod definition_used_diag_mod_inst_1755007847754_6277 (
                                                        .in_val(inj_in_val_1755007847754_550),
                                                        .out_val(inj_out_val_1755007847754_80)
                                                    );
                                                always_comb begin
                                                    inj_non_ansi_b_1755007847740_165_ts1755007847740 = reset_ts1755007847740;
                                                    inj_non_ansi_basic_output_1755007847740_316_ts1755007847740 = inj_concat_port_input_1755007847524_445_ts1755007847740;
                                                end
                                                // END: non_ansi_basic_ts1755007847740

                                                // BEGIN: buf_primitive_ts1755007847727
                                                buf b1 (inj_o_1755007847727_115, clk);
                                                // END: buf_primitive_ts1755007847727

                                                // BEGIN: ReductionOperations_ts1755007847712
                                                assign inj_and_reduce_1755007847712_210 = &intermediate_arith_ts1755007847647;
                                                assign inj_or_reduce_1755007847712_636 = |intermediate_arith_ts1755007847647;
                                                assign inj_xor_reduce_1755007847712_897 = ^intermediate_arith_ts1755007847647;
                                                // END: ReductionOperations_ts1755007847712

                                                udnt_port_module udnt_port_module_inst_1755007847699_5429 (
                                                    .uin(inj_concat_port_input_1755007847524_445),
                                                    .udnt_output(inj_udnt_output_1755007847699_685),
                                                    .uout(inj_uout_1755007847699_624),
                                                    .udnt_input(inj_concat_port_input_1755007847524_445_ts1755007847524)
                                                );
                                            assign internal_xor_res_ts1755007847686 = reset ^ clk;
                                            assign inj_o_c_1755007847685_828 = internal_xor_res_ts1755007847686 & reset;
                                            // END: module_simple_ts1755007847686

                                        always_ff @(posedge clk or posedge reset) begin
                                            if (reset) begin
                                                ff_reg_ts1755007847673 <= START_VAL;
                                                inj_out1_1755007847672_732 <= '0;
                                                inj_out2_1755007847672_118 <= '0;
                                                unused_int_var_ts1755007847673 <= 0;
                                            end else begin
                                                case ({inj_in1_1755007847672_278, inj_in2_1755007847672_279})
                                                    8'h00: ff_reg_ts1755007847673 <= ff_reg_ts1755007847673;
                                                    8'h01: ff_reg_ts1755007847673 <= inj_in1_1755007847672_278 + inj_in2_1755007847672_279;
                                                    default: ff_reg_ts1755007847673 <= MAX_COUNT;
                                                endcase
                                                inj_out1_1755007847672_732 <= ff_reg_ts1755007847673;
                                                inj_out2_1755007847672_118 <= {inj_in1_1755007847672_278[0], inj_in1_1755007847672_278[0], inj_in1_1755007847672_278[0], inj_in1_1755007847672_278[0]} | {inj_in2_1755007847672_279[3], inj_in2_1755007847672_279[2], inj_in2_1755007847672_279[1], inj_in2_1755007847672_279[0]};
                                            end
                                        end
                                        // END: ModuleFF_ts1755007847673

                                        comb_conditional comb_conditional_inst_1755007847660_6058 (
                                            .sel(inj_sel_1755007847660_801),
                                            .result1(inj_result1_1755007847660_384),
                                            .result2(inj_result2_1755007847660_742),
                                            .data1(inj_data1_1755007847660_172),
                                            .data2(inj_data2_1755007847660_338)
                                        );
                                    parameter [7:0] CONST_ZERO = 8'h00;
                                    always_comb begin
                                        intermediate_arith_ts1755007847647 = inj_in_a_1755007847643_773;
                                        intermediate_arith_ts1755007847647 = intermediate_arith_ts1755007847647 + inj_in_latch_data_1755007847524_625;
                                        intermediate_arith_ts1755007847647 = intermediate_arith_ts1755007847647 - inj_in_c_1755007847643_614;
                                        intermediate_arith_ts1755007847647 = intermediate_arith_ts1755007847647 * inj_in_const1_1755007847643_201;
                                        if (inj_in_latch_data_1755007847524_625 != CONST_ZERO) begin
                                            intermediate_arith_ts1755007847647 = intermediate_arith_ts1755007847647 / inj_in_latch_data_1755007847524_625;
                                            intermediate_arith_ts1755007847647 = intermediate_arith_ts1755007847647 % inj_in_latch_data_1755007847524_625;
                                        end else begin
                                            intermediate_arith_ts1755007847647 = 'x;
                                        end
                                        inj_out_arith_1755007847643_532 = intermediate_arith_ts1755007847647;
                                        intermediate_bitwise_ts1755007847647 = inj_in_a_1755007847643_773;
                                        intermediate_bitwise_ts1755007847647 = intermediate_bitwise_ts1755007847647 & inj_in_latch_data_1755007847524_625;
                                        intermediate_bitwise_ts1755007847647 = intermediate_bitwise_ts1755007847647 | inj_in_c_1755007847643_614;
                                        intermediate_bitwise_ts1755007847647 = intermediate_bitwise_ts1755007847647 ^ inj_in_const1_1755007847643_201;
                                        inj_out_bitwise_1755007847643_189 = intermediate_bitwise_ts1755007847647;
                                        intermediate_logical_ts1755007847647 = (inj_in_a_1755007847643_773 != CONST_ZERO) && (inj_in_latch_data_1755007847524_625 != CONST_ZERO);
                                        intermediate_logical_ts1755007847647 = intermediate_logical_ts1755007847647 || (inj_in_c_1755007847643_614 != CONST_ZERO);
                                        inj_out_logical_1755007847643_616 = !intermediate_logical_ts1755007847647;
                                        inj_out_unary_not_1755007847643_181 = ~inj_in_a_1755007847643_773;
                                        inj_out_negate_1755007847643_525 = -inj_in_a_1755007847643_773;
                                        intermediate_add_assoc_ts1755007847647 = (inj_in_a_1755007847643_773 + inj_in_latch_data_1755007847524_625) + inj_in_c_1755007847643_614;
                                        inj_out_add_assoc_1755007847643_757 = intermediate_add_assoc_ts1755007847647;
                                        intermediate_mul_assoc_ts1755007847647 = (inj_in_a_1755007847643_773 * inj_in_latch_data_1755007847524_625) * inj_in_c_1755007847643_614;
                                        inj_out_mul_assoc_1755007847643_642 = intermediate_mul_assoc_ts1755007847647;
                                        intermediate_and_assoc_ts1755007847647 = (inj_in_a_1755007847643_773 & inj_in_latch_data_1755007847524_625) & inj_in_c_1755007847643_614;
                                        inj_out_and_assoc_1755007847643_831 = intermediate_and_assoc_ts1755007847647;
                                        intermediate_or_assoc_ts1755007847647 = (inj_in_a_1755007847643_773 | inj_in_latch_data_1755007847524_625) | inj_in_c_1755007847643_614;
                                        inj_out_or_assoc_1755007847643_623 = intermediate_or_assoc_ts1755007847647;
                                        intermediate_xor_assoc_ts1755007847647 = (inj_in_a_1755007847643_773 ^ inj_in_latch_data_1755007847524_625) ^ inj_in_c_1755007847643_614;
                                        inj_out_xor_assoc_1755007847643_495 = intermediate_xor_assoc_ts1755007847647;
                                        inj_out_and_swap_const_1755007847643_250 = inj_in_const1_1755007847643_201 & inj_in_a_1755007847643_773;
                                        inj_out_or_swap_not_1755007847643_351 = (~inj_in_a_1755007847643_773) | inj_in_latch_data_1755007847524_625;
                                        inj_out_xor_swap_var_1755007847643_505 = inj_in_latch_data_1755007847524_625 ^ inj_in_c_1755007847643_614;
                                    end
                                    // END: Mod_BasicOps_ts1755007847650

                                    case_full_parallel_mod case_full_parallel_mod_inst_1755007847634_4021 (
                                        .case_expr(inj_non_ansi_i_1755007847524_50_ts1755007847524),
                                        .internal_out(inj_internal_out_1755007847634_263)
                                    );
                                    // BEGIN: typedef_union_mod_ts1755007847626
                                    typedef union packed {
                                        logic [15:0] word_ts1755007847626;
                                        logic [1:0][7:0] byte_fields_ts1755007847626;
                                    } my_packed_union_t;
                                    my_packed_union_t my_union_var;
                                    always_comb begin
                                        my_union_var.word_ts1755007847626 = inj_data0_1755007847530_108;
                                    end
                                    assign inj_field0_byte_o_1755007847626_525 = my_union_var.byte_fields_ts1755007847626[0];
                                    // END: typedef_union_mod_ts1755007847626

                                assign temp_wire_ts1755007847619 = reg_var_ts1755007847573 + inj_data_in_1755007847526_883;
                                always_comb begin
                                    inj_out1_1755007847618_488 = temp_wire_ts1755007847619;
                                end
                                // END: basic_comb_ts1755007847619

                                // BEGIN: target_module_for_bind_ts1755007847612
                                always_comb inj_o_target_result_1755007847612_15 = reg_var_ts1755007847573 + 1;
                                // END: target_module_for_bind_ts1755007847612

                                split_diff_vars_branches split_diff_vars_branches_inst_1755007847605_9908 (
                                    .in2_z(split_comb_var_ts1755007847526),
                                    .out1_z(inj_out1_z_1755007847605_767),
                                    .out2_z(inj_out2_z_1755007847605_820),
                                    .clk_z(clk),
                                    .condition_z(inj_concat_port_input_1755007847524_445_ts1755007847524),
                                    .in1_z(current_val_ts1755007847546)
                                );
                                // BEGIN: case_default_ts1755007847597
                                always_comb begin
                                    inj_out_res_1755007847597_500 = 1'b0;
                                    case (inj_non_ansi_i_1755007847524_50_ts1755007847524)
                                        2'b01: inj_out_res_1755007847597_500 = 1'b1;
                                        2'b10: inj_out_res_1755007847597_500 = 1'b0;
                                        default: inj_out_res_1755007847597_500 = 1'b1;
                                    endcase
                                end
                                // END: case_default_ts1755007847597

                                HandleOutOfBoundsRead HandleOutOfBoundsRead_inst_1755007847591_6465 (
                                    .i_addr_arr(inj_in_h_1755007847536_613),
                                    .i_addr_sel(inj_in_l_1755007847536_16),
                                    .i_vector(current_val_ts1755007847546),
                                    .o_array_var_elem(inj_o_array_var_elem_1755007847591_325),
                                    .o_sel_var_bit(inj_o_sel_var_bit_1755007847591_899)
                                );
                                // BEGIN: mismatched_width_unhandled_ts1755007847585
                                assign inj_out_1755007847585_55 = r_data_ts1755007847527;
                                // END: mismatched_width_unhandled_ts1755007847585

                                // BEGIN: mod_fixup_target_ts1755007847579
                                assign inj_fs_out_target_1755007847579_714 = inj_concat_port_input_1755007847524_445;
                                // END: mod_fixup_target_ts1755007847579

                            always_comb begin
                                reg_var_ts1755007847573  = r_data_ts1755007847527;
                                part_var_ts1755007847573 = 4'h0;
                                for (int i = 0; i < 4; i++) begin
                                    reg_var_ts1755007847573  = reg_var_ts1755007847573 + i;
                                    reg_var_ts1755007847573 += (i * 2);
                                    reg_var_ts1755007847573 <<= inj_in_shift_1755007847573_883;
                                    reg_var_ts1755007847573[i % 8] = (reg_var_ts1755007847573[i % 8] == 1'b0);
                                    reg_var_ts1755007847573[PART_START +: PART_WIDTH] = i[3:0];
                                end
                                part_var_ts1755007847573 = reg_var_ts1755007847573[7:4];
                            end
                            assign inj_out_reg_1755007847573_201  = reg_var_ts1755007847573;
                            assign inj_out_part_1755007847573_351 = part_var_ts1755007847573;
                            // END: module_assignments_in_loops_ts1755007847574

                            // BEGIN: combinatorial_logic_ts1755007847567
                            always_comb begin
                                if (inj_in_l_1755007847536_16 > 4'd5) begin
                                    inj_out_single_1755007847567_630 = 1'b1;
                                end else begin
                                    inj_out_single_1755007847567_630 = 1'b0;
                                end
                            end
                            // END: combinatorial_logic_ts1755007847567

                        always_comb begin
                            temp1_ts1755007847562 = (inj_data_in_1755007847528_275 + inj_data0_1755007847530_108) * 10;
                            if (inj_concat_port_input_1755007847524_445_ts1755007847524) begin
                                temp2_ts1755007847562 = temp1_ts1755007847562 ^ (inj_data_in_1755007847528_275 >>> 2);
                                inj_out1_1755007847562_209 = temp2_ts1755007847562 & inj_data0_1755007847530_108;
                            end else begin
                                temp2_ts1755007847562 = temp1_ts1755007847562 | (inj_data0_1755007847530_108 <<< 3);
                                inj_out1_1755007847562_209 = temp2_ts1755007847562 + inj_data_in_1755007847528_275;
                            end
                            inj_out2_1755007847562_639 = temp1_ts1755007847562 - temp2_ts1755007847562;
                        end
                        // END: procedural_complex_ts1755007847562

                    parameter int PARAM_BASIC = 42;
                    always_ff @(posedge clk) begin
                        r_state_ts1755007847558 <= ~r_state_ts1755007847558;
                    end
                    always_comb begin
                        inj_o_done_1755007847558_326 = r_state_ts1755007847558;
                    end
                    // END: mod_basic_ts1755007847558

                    LintSensitiveList LintSensitiveList_inst_1755007847555_1169 (
                        .in_p(inj_concat_port_output_1755007847524_784_ts1755007847524),
                        .in_q(inj_concat_port_input_1755007847524_445_ts1755007847524),
                        .out_r(inj_out_r_1755007847555_664)
                    );
                    target_module_for_bind target_module_for_bind_inst_1755007847552_713 (
                        .o_target_result(inj_o_target_result_1755007847552_112),
                        .i_target_clk(clk),
                        .i_target_data(current_val_ts1755007847546)
                    );
                    FunctionTaskMod FunctionTaskMod_inst_1755007847549_1437 (
                        .is_even(inj_is_even_1755007847549_598),
                        .data_in(inj_data_in_1755007847526_883)
                    );
                always_comb begin
                    current_val_ts1755007847546 = inj_in_l_1755007847536_16;
                    for (int k = 0; k < 3; k = k + 1) begin
                        current_val_ts1755007847546 = current_val_ts1755007847546 + 1;
                    end
                    inj_final_val_1755007847545_733 = current_val_ts1755007847546;
                end
                // END: loop_with_internal_assign_ts1755007847546

                // BEGIN: module_to_bind_ts1755007847543
                always_comb inj_o_bind_status_1755007847543_205 = |inj_in_l_1755007847536_16;
                // END: module_to_bind_ts1755007847543

                // BEGIN: Comb_Case_ts1755007847539
                always_comb begin
                    case (inj_in_part_lsb_1755007847524_519)
                        2'b00: inj_mux_out_1755007847538_923 = inj_in0_1755007847538_158;
                        2'b01: inj_mux_out_1755007847538_923 = inj_in1_1755007847538_641;
                        2'b10: inj_mux_out_1755007847538_923 = inj_in2_1755007847538_106;
                        default: inj_mux_out_1755007847538_923 = inj_in3_1755007847538_104;
                    endcase
                end
                // END: Comb_Case_ts1755007847539

                coalesced_assign coalesced_assign_inst_1755007847536_4568 (
                    .in_l(inj_in_l_1755007847536_16),
                    .out(inj_out_1755007847536_443),
                    .in_h(inj_in_h_1755007847536_613)
                );
                basic_d_flipflop basic_d_flipflop_inst_1755007847534_6567 (
                    .q(inj_q_1755007847534_146),
                    .clk(clk),
                    .d(inj_concat_port_input_1755007847524_445_ts1755007847524)
                );
                // BEGIN: param_local_port_ts1755007847532
                localparam int LP_BODY_VAL = 125;
                localparam int LP_CALCULATED = P_PORT_VAL + LP_BODY_VAL;
                always_comb begin
                    if (reset) begin
                        inj_o_sum_1755007847532_690 = 0;
                    end else begin
                        inj_o_sum_1755007847532_690 = LP_CALCULATED;
                    end
                end
                // END: param_local_port_ts1755007847532

                CombinationalLogicExplicit CombinationalLogicExplicit_inst_1755007847530_4494 (
                    .data1(inj_data_in_1755007847528_275),
                    .sel(inj_concat_port_input_1755007847524_445),
                    .data_out(inj_data_out_1755007847530_643),
                    .data0(inj_data0_1755007847530_108)
                );
                // BEGIN: module_conditional_write_ts1755007847529
                cond_if cif_inst();
                always_comb begin
                    if (inj_concat_port_input_1755007847524_445_ts1755007847524) begin
                        cif_inst.control_reg = inj_data_in_1755007847528_275;
                    end else begin
                        cif_inst.control_reg = 16'h0;
                    end
                    inj_control_status_1755007847528_626 = (cif_inst.control_reg != 16'h0);
                end
                // END: module_conditional_write_ts1755007847529

            always_comb begin
                r_data_ts1755007847527 = inj_in_latch_data_1755007847524_625;
            end
            assign inj_o_out_1755007847527_9 = r_data_ts1755007847527;
            // END: mod_module_attrs_ts1755007847527

        always_comb begin
            split_comb_var_ts1755007847526 = 8'b0; 
            other_comb_var_ts1755007847526 = 8'b0;
            if (inj_concat_port_output_1755007847524_784_ts1755007847524) begin
                split_comb_var_ts1755007847526 = inj_data_in_1755007847526_883;
                other_comb_var_ts1755007847526 = inj_data_in_1755007847526_883 + 1;
            end
            inj_out_a_1755007847526_576 = split_comb_var_ts1755007847526;
            inj_out_b_1755007847526_739 = other_comb_var_ts1755007847526;
        end
        // END: mod_split_comb_ts1755007847526

        mod_seq_reg mod_seq_reg_inst_1755007847525_4323 (
            .q(inj_q_1755007847525_747),
            .clk(clk),
            .d(inj_concat_port_input_1755007847524_445_ts1755007847524)
        );
        ModClockedConditional ModClockedConditional_inst_1755007847525_9228 (
            .clk(clk),
            .data_in(inj_concat_port_input_1755007847524_445_ts1755007847524),
            .enable(inj_concat_port_input_1755007847524_445),
            .data_out(inj_data_out_1755007847525_371)
        );
    assign inj_non_ansi_i_1755007847524_50_ts1755007847524 = 2'b10;
    assign inj_non_ansi_j_1755007847524_155_ts1755007847524 = 2'b01;
    assign inj_concat_port_output_1755007847524_784_ts1755007847524 = inj_concat_port_input_1755007847524_445_ts1755007847524;
    // END: non_ansi_concat_port_ts1755007847524

    module_selection module_selection_inst_1755007847524_4247 (
        .out_part_select(inj_out_part_select_1755007847524_933),
        .out_vector_assign(inj_out_vector_assign_1755007847524_942),
        .in_bit(clk),
        .in_index(inj_in_index_1755007847524_697),
        .in_part_lsb(inj_in_part_lsb_1755007847524_519),
        .in_vector(inj_in_latch_data_1755007847524_625),
        .out_bit_select(inj_out_bit_select_1755007847524_962),
        .out_bitwise_ops(inj_out_bitwise_ops_1755007847524_732)
    );
    always_latch begin
    if (clk) begin
        inj_out_latch_reg_1755007847524_37 = inj_in_latch_data_1755007847524_625;
    end
    end
    // END: module_latch_ts1755007847524
endmodule

