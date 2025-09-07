interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module SignedUnsignedConversions (
    input integer in_int,
    input logic [31:0] in_l32,
    input logic signed [7:0] in_s8,
    input logic [15:0] in_u16,
    output logic signed [15:0] out_s16,
    output logic signed [31:0] out_s32_from_int,
    output logic signed [31:0] out_s32_from_l32,
    output logic [31:0] out_u32_from_int,
    output logic [31:0] out_u32_from_l32,
    output logic [7:0] out_u8
);
    always_comb begin
        out_u8 = $unsigned(in_s8);
        out_s16 = $signed(in_u16);
        out_s32_from_l32 = $signed(in_l32);
        out_u32_from_l32 = $unsigned(in_l32);
        out_s32_from_int = $signed(in_int);
        out_u32_from_int = $unsigned(in_int);
    end
endmodule

module SimpleLogicTest (
    input bit [7:0] data_in,
    input bit select_signal,
    output bit [7:0] data_out
);
    logic [7:0] temp_data;
    always_comb begin
        if (select_signal) begin
            temp_data = data_in + 1;
        end else begin
            temp_data = data_in - 1;
        end
        data_out = temp_data;
    end
endmodule

module casez_xz_alt (
    input logic [2:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            3'b1?z: out_res = 1'b1;
            3'b0z?: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module mod_case_block_attrs (
    input wire [1:0] i_sel,
    input wire [3:0] i_val,
    output logic [3:0] o_out
);
    logic [3:0] l_temp;
    always_comb begin
        (* full_case *)
        (* parallel_case *)
        case (i_sel)
            2'b00: l_temp = i_val;
            2'b01: l_temp = i_val << 1;
            2'b10: l_temp = i_val >> 1;
            default: l_temp = 4'bxxxx;
        endcase
        (* coverage_off *)
        begin : my_named_block
            o_out = l_temp;
        end
    end
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

module module_struct (
    input wire [15:0] i_packed_data,
    output logic [7:0] o_member_sum
);
    typedef struct packed {
        logic [3:0] part1;
        logic [7:0] part2;
        logic [3:0] part3;
    } my_packed_struct_t;
    my_packed_struct_t unpacked_data;
    assign unpacked_data = i_packed_data;
    always @* begin
        o_member_sum = unpacked_data.part1 + unpacked_data.part2 + unpacked_data.part3;
    end
endmodule

module module_task_args (
    input logic [7:0] arg_in_task,
    input logic [7:0] data_a_init_task,
    input logic start_task,
    output logic [7:0] data_a_out_task,
    output logic [7:0] data_b_out_task
);
    logic [7:0] data_a ;
    logic [7:0] data_b ;
    task automatic modify_vars;
        input logic [7:0] task_arg;
        logic [7:0] task_local ;
        begin
            task_local = task_arg;
            data_a = task_local + 8'd1;
            data_b = task_arg - 8'd1;
        end
    endtask
    always_comb begin
        if (start_task) begin
            data_a = data_a_init_task;
            data_b = 8'hFF;
            modify_vars(arg_in_task);
        end else begin
            data_a = 8'h00;
            data_b = 8'h00;
        end
    end
    always_comb begin
        data_a_out_task = data_a + 8'd2;
        data_b_out_task = data_b;
    end
endmodule

module module_assign_nonblocking (
    input logic clk,
    input logic [7:0] in_value,
    input logic reset,
    output logic out_data_q
);
    my_if vif_inst();
    logic [7:0] data_q;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            vif_inst.data <= 8'h0;
            data_q <= 8'h0;
        end else begin
            vif_inst.data <= in_value;
            data_q <= vif_inst.data;
        end
    end
    assign out_data_q = data_q;
endmodule

module net_var_conn_child (
    input logic in_logic,
    output logic out_wire
);
    assign out_wire = in_logic;
endmodule

module split_complex_nb (
    input logic clk_s,
    input logic [7:0] i1_s,
    input logic [7:0] i2_s,
    input logic [7:0] i3_s,
    output logic [7:0] o1_s,
    output logic [7:0] o2_s,
    output logic [7:0] o3_s
);
    logic [7:0] t1_s, t2_s;
    always @(posedge clk_s) begin
        t1_s <= i1_s + i2_s;
        o1_s <= t1_s - i3_s;
        t2_s <= i2_s * i3_s;
        o2_s <= t1_s + t2_s;
        o3_s <= t2_s / 2;
    end
endmodule

module split_multi_nb_in_if (
    input logic clk_dd,
    input logic cond_dd,
    input logic [7:0] in1_dd,
    input logic [7:0] in2_dd,
    input logic [7:0] in3_dd,
    input logic [7:0] in4_dd,
    output logic [7:0] out1_dd,
    output logic [7:0] out2_dd
);
    always @(posedge clk_dd) begin
        if (cond_dd) begin
            out1_dd <= in1_dd + in2_dd;
            out2_dd <= in3_dd - in4_dd;
        end else begin
            out1_dd <= in1_dd * in2_dd;
            out2_dd <= in3_dd / (in4_dd + 1);
        end
    end
endmodule

module snippet #(
    parameter bit GEN = 1,
    parameter int WIDTH = 8,
    parameter int WIDTH = 8
) (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007839450_139,
    input logic inj_cond_dd_1755007839438_80,
    input wire [1:0] inj_dtl_action_sel_1755007839439_850,
    input wire [7:0] inj_dtl_data_b_1755007839439_61,
    input bit inj_enable_in_1755007839445_905,
    input logic [7:0] inj_i2_s_1755007839438_892,
    input logic [7:0] inj_i3_s_1755007839438_606,
    input wire [7:0] inj_i_in_1755007839437_36,
    input wire [15:0] inj_i_packed_data_1755007839552_550,
    input wire [3:0] inj_in0_1755007839473_803,
    input wire [3:0] inj_in1_1755007839473_283,
    input wire [3:0] inj_in2_1755007839473_427,
    input wire [3:0] inj_in3_1755007839473_928,
    input logic [7:0] inj_in4_dd_1755007839438_463,
    input integer inj_in_int_1755007839526_674,
    input logic [31:0] inj_in_l32_1755007839526_822,
    input int inj_in_val_1755007839437_522,
    input logic [2:0] inj_in_val_1755007839447_467,
    input bit [7:0] inj_in_value_1755007839543_492,
    input logic [15:0] inj_in_vector_1755007839437_262,
    input logic [31:0] inj_p_in2_1755007839660_783,
    input logic [3:0] inj_start_val_1755007839442_523,
    input wire reset,
    output logic [7:0] inj_data_a_out_task_1755007839517_175,
    output wire inj_data_b_1755007839455_661,
    output logic [7:0] inj_data_b_out_task_1755007839517_98,
    output logic [3:0] inj_data_out1_n_1755007839636_297,
    output logic [3:0] inj_data_out2_n_1755007839636_764,
    output bit [7:0] inj_data_out_1755007839593_184,
    output logic [7:0] inj_dout_1755007839573_493,
    output logic [7:0] inj_dtl_result_reg_1755007839439_395,
    output logic inj_dummy_out_1755007839478_55,
    output logic inj_dummy_out_1755007839496_271,
    output bit inj_dummy_out_1755007839503_618,
    output logic inj_dummy_out_1755007839582_735,
    output logic [7:0] inj_field0_byte_o_1755007839672_621,
    output logic [7:0] inj_field2_o_1755007839563_800,
    output logic [7:0] inj_final_val_1755007839442_323,
    output logic [7:0] inj_final_val_1755007839490_351,
    output logic [4:0] inj_internal_out_1755007839450_789,
    output reg [3:0] inj_mux_out_1755007839473_474,
    output logic [7:0] inj_o1_s_1755007839438_564,
    output logic [7:0] inj_o2_s_1755007839438_779,
    output logic [7:0] inj_o3_s_1755007839438_620,
    output logic [7:0] inj_o_member_sum_1755007839552_232,
    output logic [7:0] inj_o_out_1755007839437_83,
    output logic inj_o_out_1755007839461_566,
    output logic [3:0] inj_o_out_1755007839603_214,
    output wire [7:0] inj_out1_1755007839483_711,
    output logic [7:0] inj_out1_dd_1755007839438_909,
    output wire [7:0] inj_out2_1755007839483_717,
    output logic [7:0] inj_out2_dd_1755007839438_843,
    output bit inj_out_1755007839445_554,
    output logic inj_out_1755007839625_318,
    output bit [2:0] inj_out_category_1755007839543_560,
    output logic [7:0] inj_out_data_1755007839496_99,
    output logic [7:0] inj_out_data_1755007839582_308,
    output logic inj_out_data_q_1755007839510_857,
    output reg inj_out_res_1755007839447_771,
    output logic signed [15:0] inj_out_s16_1755007839526_582,
    output logic signed [31:0] inj_out_s32_from_int_1755007839526_872,
    output logic signed [31:0] inj_out_s32_from_l32_1755007839526_121,
    output logic [7:0] inj_out_slice_1755007839437_646,
    output logic inj_out_sub_1755007839614_366,
    output logic [31:0] inj_out_u32_from_int_1755007839526_40,
    output logic [31:0] inj_out_u32_from_l32_1755007839526_192,
    output logic [7:0] inj_out_u8_1755007839526_958,
    output int inj_out_val_1755007839437_875,
    output logic inj_out_valid_1755007839458_663,
    output logic inj_out_valid_1755007839496_255,
    output logic inj_out_valid_1755007839582_163,
    output logic inj_out_wire_1755007839469_514,
    output logic [7:0] inj_out_x_j_1755007839534_446,
    output logic [7:0] inj_out_y_j_1755007839534_231,
    output logic [31:0] inj_p_out_1755007839660_866,
    output logic inj_sig_out_1755007839465_457,
    output logic inj_unused_out_1755007839647_741
);
    // BEGIN: mod_module_attrs_ts1755007839437
    logic [WIDTH-1:0] r_data_ts1755007839437;
        // BEGIN: deep_task_logic_ts1755007839440
        task automatic perform_action;
            input [7:0] in_a;
            input [7:0] in_b;
            input [1:0] action;
            output logic [7:0] calculated_res_ts1755007839440;
            logic [7:0] temp_task_calc_ts1755007839440;
            if (action[0]) begin
                if (action[1]) begin
                    temp_task_calc_ts1755007839440 = in_a + in_b;
                end else begin
                    temp_task_calc_ts1755007839440 = in_a - in_b;
                end
            end else begin
                if (action[1]) begin
                    temp_task_calc_ts1755007839440 = in_a & in_b;
                end else begin
                    temp_task_calc_ts1755007839440 = in_a | in_b;
                end
            end
            case (temp_task_calc_ts1755007839440[1:0])
                2'b00: calculated_res_ts1755007839440 = temp_task_calc_ts1755007839440 ^ 8'hFF;
                2'b01: calculated_res_ts1755007839440 = temp_task_calc_ts1755007839440 + 1;
                2'b10: calculated_res_ts1755007839440 = temp_task_calc_ts1755007839440 - 1;
                default: calculated_res_ts1755007839440 = temp_task_calc_ts1755007839440;
            endcase
        endtask
        always_ff @(posedge clk or negedge reset) begin
            if (!reset) begin
                inj_dtl_result_reg_1755007839439_395 <= 8'd0;
            end else begin
                logic [7:0] next_dtl_result_ts1755007839440;
                    // BEGIN: loop_with_internal_assign_ts1755007839443
                    logic [7:0] current_val_ts1755007839443;
                        // BEGIN: ModuleImplicitPort_ts1755007839458
                        logic valid_ts1755007839458;
                            // BEGIN: name_conflict_example_ts1755007839461
                            parameter int my_param = 5;
                            logic my_var_ts1755007839461;
                                // BEGIN: mixed_conn_child_ts1755007839478
                                logic dummy_internal_ts1755007839478;
                                    // BEGIN: multi_always_comb_ts1755007839483
                                    logic [7:0] intermediate1_ts1755007839483;
                                    logic [7:0] intermediate2_ts1755007839483;
                                        // BEGIN: loop_with_internal_assign_ts1755007839491
                                        logic [7:0] current_val_ts1755007839490;
                                            // BEGIN: split_multiple_blocking_ts1755007839636
                                            logic [3:0] temp_n_ts1755007839636;
                                                // BEGIN: typedef_union_mod_ts1755007839672
                                                typedef union packed {
                                                    logic [15:0] word_ts1755007839672;
                                                    logic [1:0][7:0] byte_fields_ts1755007839672;
                                                } my_packed_union_t;
                                                my_packed_union_t my_union_var;
                                                always_comb begin
                                                    my_union_var.word_ts1755007839672 = inj_in_vector_1755007839437_262;
                                                end
                                                assign inj_field0_byte_o_1755007839672_621 = my_union_var.byte_fields_ts1755007839672[0];
                                                // END: typedef_union_mod_ts1755007839672

                                                // BEGIN: more_procedural_ts1755007839660
                                                always_comb begin
                                                    case (inj_case_expr_1755007839450_139)
                                                        2'b00: inj_p_out_1755007839660_866 = (inj_in_l32_1755007839526_822 + inj_p_in2_1755007839660_783) * 2;
                                                        2'b01: inj_p_out_1755007839660_866 = (inj_in_l32_1755007839526_822 - inj_p_in2_1755007839660_783) / 3; 
                                                        2'b10: inj_p_out_1755007839660_866 = (inj_in_l32_1755007839526_822 << 4) | (inj_p_in2_1755007839660_783 >> 2);
                                                        default: inj_p_out_1755007839660_866 = ~(inj_in_l32_1755007839526_822 ^ inj_p_in2_1755007839660_783) + 1;
                                                    endcase
                                                end
                                                // END: more_procedural_ts1755007839660

                                                // BEGIN: unreferenced_module_ts1755007839647
                                                assign inj_unused_out_1755007839647_741 = ~dummy_internal_ts1755007839478;
                                                // END: unreferenced_module_ts1755007839647

                                            always @(*) begin
                                                temp_n_ts1755007839636 = inj_start_val_1755007839442_523 + 1;
                                                inj_data_out1_n_1755007839636_297 = temp_n_ts1755007839636 * 2;
                                                inj_data_out2_n_1755007839636_764 = temp_n_ts1755007839636 + 3;
                                            end
                                            // END: split_multiple_blocking_ts1755007839636

                                            // BEGIN: reduction_ops_ts1755007839625
                                            assign inj_out_1755007839625_318 = &intermediate2_ts1755007839483 | ^current_val_ts1755007839490;
                                            // END: reduction_ops_ts1755007839625

                                            // BEGIN: mod_sub_ts1755007839614
                                            assign inj_out_sub_1755007839614_366 = reset;
                                            // END: mod_sub_ts1755007839614

                                            mod_case_block_attrs mod_case_block_attrs_inst_1755007839603_3359 (
                                                .o_out(inj_o_out_1755007839603_214),
                                                .i_sel(inj_dtl_action_sel_1755007839439_850),
                                                .i_val(inj_in1_1755007839473_283)
                                            );
                                            SimpleLogicTest SimpleLogicTest_inst_1755007839593_9863 (
                                                .data_in(inj_in_value_1755007839543_492),
                                                .select_signal(inj_enable_in_1755007839445_905),
                                                .data_out(inj_data_out_1755007839593_184)
                                            );
                                            // BEGIN: virtual_interface_lookup_mod_ts1755007839583
                                            always_comb begin
                                                inj_out_data_1755007839582_308  = next_dtl_result_ts1755007839440;
                                                inj_out_valid_1755007839582_163 = my_var_ts1755007839461;
                                                inj_dummy_out_1755007839582_735 = dummy_internal_ts1755007839478;
                                            end
                                            // END: virtual_interface_lookup_mod_ts1755007839583

                                            // BEGIN: Parameterized_ts1755007839573
                                            assign inj_dout_1755007839573_493 = current_val_ts1755007839490;
                                            // END: Parameterized_ts1755007839573

                                            // BEGIN: typedef_struct_mod_ts1755007839563
                                            typedef struct packed {
                                                logic [7:0] field1_ts1755007839563;
                                                logic [7:0] field2_ts1755007839563;
                                            } my_packed_struct_t;
                                            my_packed_struct_t my_struct_var;
                                            always_comb begin
                                                my_struct_var = inj_in_vector_1755007839437_262;
                                            end
                                            assign inj_field2_o_1755007839563_800 = my_struct_var.field2_ts1755007839563;
                                            // END: typedef_struct_mod_ts1755007839563

                                            module_struct module_struct_inst_1755007839552_3064 (
                                                .i_packed_data(inj_i_packed_data_1755007839552_550),
                                                .o_member_sum(inj_o_member_sum_1755007839552_232)
                                            );
                                            mod_if_elseif_chained mod_if_elseif_chained_inst_1755007839543_1887 (
                                                .in_value(inj_in_value_1755007839543_492),
                                                .out_category(inj_out_category_1755007839543_560)
                                            );
                                            // BEGIN: split_multiple_in_branch_ts1755007839534
                                            always @(posedge clk) begin
                                                if (dummy_internal_ts1755007839478) begin
                                                    inj_out_x_j_1755007839534_446 <= intermediate2_ts1755007839483 * 3;
                                                    inj_out_y_j_1755007839534_231 <= next_dtl_result_ts1755007839440 + 1;
                                                end else begin
                                                    inj_out_x_j_1755007839534_446 <= intermediate2_ts1755007839483;
                                                    inj_out_y_j_1755007839534_231 <= next_dtl_result_ts1755007839440;
                                                end
                                            end
                                            // END: split_multiple_in_branch_ts1755007839534

                                            SignedUnsignedConversions SignedUnsignedConversions_inst_1755007839526_2809 (
                                                .out_s32_from_l32(inj_out_s32_from_l32_1755007839526_121),
                                                .out_u32_from_int(inj_out_u32_from_int_1755007839526_40),
                                                .out_u8(inj_out_u8_1755007839526_958),
                                                .in_u16(inj_in_vector_1755007839437_262),
                                                .out_s16(inj_out_s16_1755007839526_582),
                                                .in_l32(inj_in_l32_1755007839526_822),
                                                .out_u32_from_l32(inj_out_u32_from_l32_1755007839526_192),
                                                .in_s8(current_val_ts1755007839443),
                                                .in_int(inj_in_int_1755007839526_674),
                                                .out_s32_from_int(inj_out_s32_from_int_1755007839526_872)
                                            );
                                            module_task_args module_task_args_inst_1755007839517_3365 (
                                                .data_a_init_task(current_val_ts1755007839490),
                                                .start_task(valid_ts1755007839458),
                                                .data_a_out_task(inj_data_a_out_task_1755007839517_175),
                                                .data_b_out_task(inj_data_b_out_task_1755007839517_98),
                                                .arg_in_task(inj_i3_s_1755007839438_606)
                                            );
                                            module_assign_nonblocking module_assign_nonblocking_inst_1755007839510_9320 (
                                                .out_data_q(inj_out_data_q_1755007839510_857),
                                                .clk(clk),
                                                .in_value(current_val_ts1755007839490),
                                                .reset(reset)
                                            );
                                            // BEGIN: module_finish_numbers_ts1755007839503
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
                                            assign inj_dummy_out_1755007839503_618 = inj_enable_in_1755007839445_905;
                                            // END: module_finish_numbers_ts1755007839503

                                            // BEGIN: virtual_interface_lookup_mod_ts1755007839496
                                            always_comb begin
                                                inj_out_data_1755007839496_99  = next_dtl_result_ts1755007839440;
                                                inj_out_valid_1755007839496_255 = dummy_internal_ts1755007839478;
                                                inj_dummy_out_1755007839496_271 = my_var_ts1755007839461;
                                            end
                                            // END: virtual_interface_lookup_mod_ts1755007839496

                                        always_comb begin
                                            current_val_ts1755007839490 = inj_start_val_1755007839442_523;
                                            for (int k = 0; k < 3; k = k + 1) begin
                                                current_val_ts1755007839490 = current_val_ts1755007839490 + 1;
                                            end
                                            inj_final_val_1755007839490_351 = current_val_ts1755007839490;
                                        end
                                        // END: loop_with_internal_assign_ts1755007839491

                                    always @(*) begin
                                        intermediate1_ts1755007839483 = inj_i_in_1755007839437_36 & inj_dtl_data_b_1755007839439_61;
                                    end
                                    always @(*) begin
                                        intermediate2_ts1755007839483 = inj_i_in_1755007839437_36 | inj_dtl_data_b_1755007839439_61;
                                    end
                                    assign inj_out1_1755007839483_711 = intermediate1_ts1755007839483 + 8'd1;
                                    assign inj_out2_1755007839483_717 = intermediate2_ts1755007839483 - 8'd1;
                                    // END: multi_always_comb_ts1755007839483

                                always_comb dummy_internal_ts1755007839478 = |current_val_ts1755007839443 | my_var_ts1755007839461;
                                assign inj_dummy_out_1755007839478_55 = dummy_internal_ts1755007839478;
                                // END: mixed_conn_child_ts1755007839478

                                // BEGIN: Comb_Case_ts1755007839473
                                always_comb begin
                                    case (inj_dtl_action_sel_1755007839439_850)
                                        2'b00: inj_mux_out_1755007839473_474 = inj_in0_1755007839473_803;
                                        2'b01: inj_mux_out_1755007839473_474 = inj_in1_1755007839473_283;
                                        2'b10: inj_mux_out_1755007839473_474 = inj_in2_1755007839473_427;
                                        default: inj_mux_out_1755007839473_474 = inj_in3_1755007839473_928;
                                    endcase
                                end
                                // END: Comb_Case_ts1755007839473

                                net_var_conn_child net_var_conn_child_inst_1755007839469_3272 (
                                    .in_logic(inj_cond_dd_1755007839438_80),
                                    .out_wire(inj_out_wire_1755007839469_514)
                                );
                                // BEGIN: GenerateIfParam_ts1755007839465
                                generate
                                    if (GEN) begin : g_true
                                        assign inj_sig_out_1755007839465_457 = inj_cond_dd_1755007839438_80;
                                    end
                                    else begin : g_false
                                        assign inj_sig_out_1755007839465_457 = ~inj_cond_dd_1755007839438_80;
                                    end
                                endgenerate
                                // END: GenerateIfParam_ts1755007839465

                            always_comb my_var_ts1755007839461 = valid_ts1755007839458;
                            assign inj_o_out_1755007839461_566 = valid_ts1755007839458 && (my_param == 5) && my_var_ts1755007839461;
                            // END: name_conflict_example_ts1755007839461

                        assign valid_ts1755007839458 = |next_dtl_result_ts1755007839440;
                        assign inj_out_valid_1755007839458_663 = valid_ts1755007839458;
                        // END: ModuleImplicitPort_ts1755007839458

                        // BEGIN: simple_logic_a_ts1755007839455
                        assign inj_data_b_1755007839455_661 = ~clk;
                        // END: simple_logic_a_ts1755007839455

                        // BEGIN: case_unique0_violating_mod_ts1755007839450
                        always @* begin
                            unique0 casez (inj_case_expr_1755007839450_139)
                                2'b1?: inj_internal_out_1755007839450_789 = 8;
                                2'b11: inj_internal_out_1755007839450_789 = 9;  
                                2'b?1: inj_internal_out_1755007839450_789 = 10; 
                                2'b00: inj_internal_out_1755007839450_789 = 11; 
                            endcase
                        end
                        // END: case_unique0_violating_mod_ts1755007839450

                        casez_xz_alt casez_xz_alt_inst_1755007839447_3286 (
                            .in_val(inj_in_val_1755007839447_467),
                            .out_res(inj_out_res_1755007839447_771)
                        );
                        // BEGIN: mod_default_disable_ts1755007839445
                        assign inj_out_1755007839445_554 = inj_enable_in_1755007839445_905;
                        // END: mod_default_disable_ts1755007839445

                    always_comb begin
                        current_val_ts1755007839443 = inj_start_val_1755007839442_523;
                        for (int k = 0; k < 3; k = k + 1) begin
                            current_val_ts1755007839443 = current_val_ts1755007839443 + 1;
                        end
                        inj_final_val_1755007839442_323 = current_val_ts1755007839443;
                    end
                    // END: loop_with_internal_assign_ts1755007839443

                if (reset) begin
                    perform_action(inj_i_in_1755007839437_36, inj_dtl_data_b_1755007839439_61, inj_dtl_action_sel_1755007839439_850, next_dtl_result_ts1755007839440);
                end else begin
                    next_dtl_result_ts1755007839440 = inj_dtl_result_reg_1755007839439_395;
                end
                inj_dtl_result_reg_1755007839439_395 <= next_dtl_result_ts1755007839440;
            end
        end
        // END: deep_task_logic_ts1755007839440

        split_multi_nb_in_if split_multi_nb_in_if_inst_1755007839438_5775 (
            .clk_dd(clk),
            .cond_dd(inj_cond_dd_1755007839438_80),
            .in1_dd(inj_i2_s_1755007839438_892),
            .in2_dd(r_data_ts1755007839437),
            .in3_dd(inj_i3_s_1755007839438_606),
            .in4_dd(inj_in4_dd_1755007839438_463),
            .out1_dd(inj_out1_dd_1755007839438_909),
            .out2_dd(inj_out2_dd_1755007839438_843)
        );
        split_complex_nb split_complex_nb_inst_1755007839438_5308 (
            .i1_s(r_data_ts1755007839437),
            .i2_s(inj_i2_s_1755007839438_892),
            .i3_s(inj_i3_s_1755007839438_606),
            .o1_s(inj_o1_s_1755007839438_564),
            .o2_s(inj_o2_s_1755007839438_779),
            .o3_s(inj_o3_s_1755007839438_620),
            .clk_s(clk)
        );
        // BEGIN: MiscExpressions_ValueRange_ts1755007839437
        always_comb begin
            inj_out_slice_1755007839437_646 = inj_in_vector_1755007839437_262[7:0];
        end
        // END: MiscExpressions_ValueRange_ts1755007839437

        // BEGIN: simple_undeclared_mod_ts1755007839437
        assign inj_out_val_1755007839437_875 = inj_in_val_1755007839437_522;
        // END: simple_undeclared_mod_ts1755007839437

    always_comb begin
        r_data_ts1755007839437 = inj_i_in_1755007839437_36;
    end
    assign inj_o_out_1755007839437_83 = r_data_ts1755007839437;
    // END: mod_module_attrs_ts1755007839437
endmodule

