interface simple_if (
    input logic clk
);
    logic data;
    logic ready;
    modport master (output data, input ready);
    modport slave (input data, output ready);
endinterface
module ConditionalOps (
    input logic sel,
    input int val_false,
    input int val_true,
    output int out_val
);
    assign out_val = sel ? val_true : val_false;
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

module mod_event_implicit (
    input wire [3:0] data_in,
    output reg [3:0] data_out
);
    always @* begin
        data_out = data_in;
    end
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

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module simple_logic_b (
    input wire data_c,
    output wire data_d
);
    assign data_d = data_c;
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

module sub_module (
    input logic sub_in,
    output logic sub_out
);
    assign sub_out = !sub_in;
endmodule

module snippet #(
    parameter int SEL_PARAM = 6,
    parameter int SEL_PARAM = 5
) (
    input wire clk,
    input wire [3:0] inj_data_in_1755007760518_322,
    input logic [3:0] inj_data_in_1755007760521_154,
    input bit [7:0] inj_data_in_1755007760536_306,
    input wire [31:0] inj_data_in_1755007760546_882,
    input logic inj_i_control_1755007760518_558,
    input logic inj_i_in_1755007760518_944,
    input wire [1:0] inj_in_const_index_1755007760519_835,
    input wire [7:0] inj_in_data_1755007760519_115,
    input wire [1:0] inj_in_index_1755007760519_551,
    input logic [2:0] inj_in_val_1755007760524_77,
    input logic [15:0] inj_in_vec_1755007760518_749,
    input logic [15:0] inj_numerator_1755007760555_281,
    input int inj_sel_in_1755007760521_611,
    input bit inj_select_signal_1755007760536_279,
    input wire reset,
    output logic [7:0] inj_byte_out_1755007760570_645,
    output logic inj_concat_port_output_1755007760527_735,
    output wire inj_data_d_1755007760551_996,
    output reg [3:0] inj_data_out_1755007760518_311,
    output logic [7:0] inj_data_out_1755007760521_219,
    output bit [7:0] inj_data_out_1755007760536_644,
    output logic inj_data_out_1755007760542_473,
    output logic [31:0] inj_data_out_1755007760546_621,
    output logic [7:0] inj_data_out_1755007760574_78,
    output logic [7:0] inj_data_out_1755007760585_72,
    output logic inj_is_even_1755007760539_403,
    output logic [7:0] inj_left_shift_log_1755007760531_846,
    output logic inj_main_out_1755007760560_897,
    output logic [1:0] inj_non_ansi_i_1755007760527_744,
    output logic [1:0] inj_non_ansi_j_1755007760527_736,
    output logic inj_o_bind_status_1755007760567_475,
    output logic inj_o_out_1755007760518_946,
    output logic [7:0] inj_out_array_sel_const_1755007760519_672,
    output logic [7:0] inj_out_array_sel_var_1755007760519_747,
    output logic inj_out_la_1755007760519_564,
    output logic [7:0] inj_out_reg_h_1755007760533_933,
    output reg inj_out_res_1755007760524_499,
    output logic [7:0] inj_out_slice_be_1755007760518_718,
    output logic [7:0] inj_out_slice_le_1755007760518_897,
    output int inj_out_val_1755007760580_249,
    output logic [15:0] inj_packed_out_1755007760570_855,
    output logic inj_q_1755007760523_571,
    output logic [15:0] inj_quotient_1755007760555_559,
    output logic [7:0] inj_remainder_1755007760555_212,
    output logic [7:0] inj_right_shift_arith_1755007760531_385,
    output logic [7:0] inj_right_shift_log_1755007760531_380,
    output logic inj_sum_1755007760520_756
);
    // BEGIN: attributes_on_expr_port_ts1755007760518
    logic internal_sig_ts1755007760518;
        // BEGIN: Mod_ArrayOps_ts1755007760519
        logic [7:0] my_array_ts1755007760519 [3:0];
            // BEGIN: ModuleHierarchy_High_ts1755007760522
            ModuleBasic m1 (
                .a      (1'b1),
                .b      (inj_sel_in_1755007760521_611),
                .out_a  (),
                .out_b  ( )
            );
            if (SEL_PARAM > 5) begin : gen_high
                int high_data_ts1755007760521;
                ModuleBasic m_high (
                    .a      (1'b0),
                    .b      (SEL_PARAM),
                    .out_a  (),
                    .out_b  (high_data_ts1755007760521)
                );
            end else begin : gen_low
                int low_data_ts1755007760521;
                ModuleBasic m_low (
                    .a      (1'b0),
                    .b      (SEL_PARAM),
                    .out_a  (),
                    .out_b  (low_data_ts1755007760521)
                );
            end
            for (genvar i = 0; i < 2; ++i) begin : gen_loop
                logic [1:0] sub_in_ts1755007760521;
                assign sub_in_ts1755007760521 = inj_data_in_1755007760521_154[i*2 +: 2];
                int temp_int_ts1755007760521;
                    // BEGIN: non_ansi_concat_port_ts1755007760528
                    output logic [1:0] inj_non_ansi_i_1755007760527_744_ts1755007760527;
                    output logic [1:0] inj_non_ansi_j_1755007760527_736_ts1755007760527;
                    input logic inj_i_control_1755007760518_558_ts1755007760527;
                    output logic inj_concat_port_output_1755007760527_735_ts1755007760527;
                        // BEGIN: SimpleLogicTest_ts1755007760536
                        logic [7:0] temp_data_ts1755007760536;
                            // BEGIN: mod_part_select_ts1755007760547
                            logic [31:0] temp_reg_ts1755007760547;
                                // BEGIN: ModuleHierarchy_Low_ts1755007760586
                                ModuleBasic m1 (
                                    .a     (1'b1),
                                    .b     (inj_sel_in_1755007760521_611),
                                    .out_a (),
                                    .out_b ( )
                                );
                                if (SEL_PARAM > 5) begin : gen_high
                                    int high_data_ts1755007760586;
                                    ModuleBasic m_high (
                                        .a     (1'b0),
                                        .b     (SEL_PARAM),
                                        .out_a (),
                                        .out_b (high_data_ts1755007760586)
                                    );
                                end else begin : gen_low
                                    int low_data_ts1755007760586;
                                    ModuleBasic m_low (
                                        .a     (1'b0),
                                        .b     (SEL_PARAM),
                                        .out_a (),
                                        .out_b (low_data_ts1755007760586)
                                    );
                                end
                                for (genvar i = 0; i < 2; ++i) begin : gen_loop
                                    logic [1:0] sub_in_ts1755007760586;
                                    assign sub_in_ts1755007760586 = inj_data_in_1755007760521_154[i*2 +: 2];
                                    int temp_int_ts1755007760586;
                                    ModuleBasic m_inst (
                                        .a      (1'b0),
                                        .b      (int'(sub_in_ts1755007760586)),
                                        .out_a  (),
                                        .out_b  (temp_int_ts1755007760586)
                                    );
                                    assign inj_data_out_1755007760585_72[i*4 +: 4] = temp_int_ts1755007760586[3:0];
                                end
                                // END: ModuleHierarchy_Low_ts1755007760586

                                ConditionalOps ConditionalOps_inst_1755007760580_158 (
                                    .sel(inj_i_in_1755007760518_944),
                                    .val_false(temp_int_ts1755007760521),
                                    .val_true(inj_sel_in_1755007760521_611),
                                    .out_val(inj_out_val_1755007760580_249)
                                );
                                // BEGIN: cu_base_ts1755007760574
                                assign inj_data_out_1755007760574_78 = my_array_ts1755007760519;
                                // END: cu_base_ts1755007760574

                                // BEGIN: PackedStructOps_ts1755007760570
                                typedef struct packed {
                                    logic [7:0] low_ts1755007760570;
                                    logic [7:0] high_ts1755007760570;
                                } pair_t;
                                pair_t data_pair;
                                assign data_pair.high_ts1755007760570 = inj_in_vec_1755007760518_749[15:8];
                                assign data_pair.low_ts1755007760570 = my_array_ts1755007760519;
                                assign inj_byte_out_1755007760570_645 = data_pair.high_ts1755007760570;
                                assign inj_packed_out_1755007760570_855[15:8] = data_pair.high_ts1755007760570;
                                assign inj_packed_out_1755007760570_855[7:0] = data_pair.low_ts1755007760570 + my_array_ts1755007760519;
                                // END: PackedStructOps_ts1755007760570

                                // BEGIN: module_to_bind_ts1755007760567
                                always_comb inj_o_bind_status_1755007760567_475 = |inj_data_in_1755007760521_154;
                                // END: module_to_bind_ts1755007760567

                                // BEGIN: hierarchy_if_ts1755007760560
                                sub_module u_sub (
                                    .sub_in(inj_concat_port_output_1755007760527_735_ts1755007760527),
                                    .sub_out(inj_main_out_1755007760560_897)
                                );
                                simple_if if_inst (.clk(clk));
                                always_comb begin
                                    if_inst.data = inj_concat_port_output_1755007760527_735_ts1755007760527;
                                    if_inst.ready = inj_main_out_1755007760560_897;
                                end
                                // END: hierarchy_if_ts1755007760560

                                // BEGIN: div_mod_ops_ts1755007760555
                                assign inj_quotient_1755007760555_559 = (my_array_ts1755007760519 == 0) ? 16'hFFFF : (inj_numerator_1755007760555_281 / my_array_ts1755007760519); 
                                assign inj_remainder_1755007760555_212 = (temp_data_ts1755007760536 == 0) ? 8'hFF : (inj_in_vec_1755007760518_749 % temp_data_ts1755007760536);
                                // END: div_mod_ops_ts1755007760555

                                simple_logic_b simple_logic_b_inst_1755007760551_5060 (
                                    .data_c(clk),
                                    .data_d(inj_data_d_1755007760551_996)
                                );
                            always_comb begin
                                temp_reg_ts1755007760547[7:0] = inj_data_in_1755007760546_882[7:0];
                                temp_reg_ts1755007760547[15:8] = inj_data_in_1755007760546_882[23:16];
                                temp_reg_ts1755007760547[31:16] = inj_data_in_1755007760546_882[15:0];
                                temp_reg_ts1755007760547[0] = inj_data_in_1755007760546_882[31];
                                temp_reg_ts1755007760547[8] = inj_data_in_1755007760546_882[0];
                                inj_data_out_1755007760546_621 = temp_reg_ts1755007760547;
                            end
                            // END: mod_part_select_ts1755007760547

                            // BEGIN: sequential_register_ts1755007760543
                            always_ff @(posedge clk or negedge reset) begin
                                if (!reset) begin
                                    inj_data_out_1755007760542_473 <= 1'b0; 
                                end else if (inj_i_control_1755007760518_558_ts1755007760527) begin
                                    inj_data_out_1755007760542_473 <= inj_concat_port_output_1755007760527_735_ts1755007760527; 
                                end
                            end
                            // END: sequential_register_ts1755007760543

                            // BEGIN: FunctionTaskMod_ts1755007760539
                            function automatic bit check_even(input logic [7:0] v);
                                check_even = ~v[0];
                            endfunction
                            task automatic dummy_task(input logic [7:0] v);
                                int tmp_ts1755007760539;
                                tmp_ts1755007760539 = v;
                            endtask
                            assign inj_is_even_1755007760539_403 = check_even(temp_data_ts1755007760536);
                            // END: FunctionTaskMod_ts1755007760539

                        always_comb begin
                            if (inj_select_signal_1755007760536_279) begin
                                temp_data_ts1755007760536 = inj_data_in_1755007760536_306 + 1;
                            end else begin
                                temp_data_ts1755007760536 = inj_data_in_1755007760536_306 - 1;
                            end
                            inj_data_out_1755007760536_644 = temp_data_ts1755007760536;
                        end
                        // END: SimpleLogicTest_ts1755007760536

                        split_if_only_then split_if_only_then_inst_1755007760533_3165 (
                            .clk_h(clk),
                            .condition_h(inj_i_control_1755007760518_558_ts1755007760527),
                            .in_val_h(my_array_ts1755007760519),
                            .out_reg_h(inj_out_reg_h_1755007760533_933)
                        );
                        // BEGIN: ShiftOperations_ts1755007760531
                        assign inj_left_shift_log_1755007760531_846 = my_array_ts1755007760519 << inj_in_val_1755007760524_77;
                        assign inj_right_shift_log_1755007760531_380 = my_array_ts1755007760519 >> inj_in_val_1755007760524_77;
                        assign inj_right_shift_arith_1755007760531_385 = $signed(my_array_ts1755007760519) >>> inj_in_val_1755007760524_77;
                        // END: ShiftOperations_ts1755007760531

                    assign inj_non_ansi_i_1755007760527_744_ts1755007760527 = 2'b10;
                    assign inj_non_ansi_j_1755007760527_736_ts1755007760527 = 2'b01;
                    assign inj_concat_port_output_1755007760527_735_ts1755007760527 = inj_i_control_1755007760518_558_ts1755007760527;
                    // END: non_ansi_concat_port_ts1755007760528

                    // BEGIN: casez_xz_ts1755007760525
                    always_comb begin
                        inj_out_res_1755007760524_499 = 1'b0;
                        casez (inj_in_val_1755007760524_77)
                            3'b1??: inj_out_res_1755007760524_499 = 1'b1;
                            3'b0z?: inj_out_res_1755007760524_499 = 1'b0;
                            default: inj_out_res_1755007760524_499 = 1'b1;
                        endcase
                    end
                    // END: casez_xz_ts1755007760525

                    mod_seq_reg mod_seq_reg_inst_1755007760523_5993 (
                        .q(inj_q_1755007760523_571),
                        .clk(clk),
                        .d(inj_i_in_1755007760518_944)
                    );
                ModuleBasic m_inst (
                    .a      (1'b0),
                    .b      (int'(sub_in_ts1755007760521)),
                    .out_a  (),
                    .out_b  (temp_int_ts1755007760521)
                );
                assign inj_data_out_1755007760521_219[i*4 +: 4] = temp_int_ts1755007760521[3:0];
            end
            // END: ModuleHierarchy_High_ts1755007760522

            // BEGIN: simple_adder_ts1755007760520
            assign inj_sum_1755007760520_756 = inj_i_control_1755007760518_558 + internal_sig_ts1755007760518;
            // END: simple_adder_ts1755007760520

        always_comb begin
            my_array_ts1755007760519[0] = inj_in_data_1755007760519_115;
            my_array_ts1755007760519[1] = inj_in_data_1755007760519_115 + 8'd1;
            my_array_ts1755007760519[2] = inj_in_data_1755007760519_115 + 8'd2;
            my_array_ts1755007760519[3] = inj_in_data_1755007760519_115 + 8'd3;
            inj_out_array_sel_var_1755007760519_747 = my_array_ts1755007760519[inj_in_index_1755007760519_551];
            inj_out_array_sel_const_1755007760519_672 = my_array_ts1755007760519[inj_in_const_index_1755007760519_835];
        end
        // END: Mod_ArrayOps_ts1755007760519

        // BEGIN: mod_large_array_target_ts1755007760519
        assign inj_out_la_1755007760519_564 = inj_i_in_1755007760518_944;
        // END: mod_large_array_target_ts1755007760519

        // BEGIN: range_select_simple_packed_ts1755007760518
        assign inj_out_slice_be_1755007760518_718 = inj_in_vec_1755007760518_749[7:0]; 
        assign inj_out_slice_le_1755007760518_897 = inj_in_vec_1755007760518_749[7:0]; 
        // END: range_select_simple_packed_ts1755007760518

    assign internal_sig_ts1755007760518 = inj_i_in_1755007760518_944 & inj_i_control_1755007760518_558;
    simple_adder sa_inst(
        .a  (inj_i_in_1755007760518_944),
        (* fanout_limit = 10 *) .b(inj_i_control_1755007760518_558),
        .sum(inj_o_out_1755007760518_946)
    );
    // END: attributes_on_expr_port_ts1755007760518

    mod_event_implicit mod_event_implicit_inst_1755007760518_839 (
        .data_in(inj_data_in_1755007760518_322),
        .data_out(inj_data_out_1755007760518_311)
    );
endmodule

