module LintSensitiveList (
    input logic in_p,
    input logic in_q,
    output logic out_r
);
    always_comb begin
        out_r = in_p | in_q;
    end
endmodule

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module sequential_always_assign (
    input logic clk,
    input logic [7:0] in,
    output logic [7:0] out
);
    always @(posedge clk) begin
        out <= in;
    end
endmodule

module simple_xor_gate (
    input logic in1,
    input logic in2,
    output logic out
);
    assign out = in1 ^ in2;
endmodule

module timed_assign_unhandled (
    input logic clk,
    input logic [7:0] in,
    output logic [7:0] out
);
    always @(posedge clk) begin
        out <= in;
    end
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_control_1755007804603_278,
    input bit [7:0] inj_data1_1755007804613_894,
    input bit [7:0] inj_data2_1755007804613_82,
    input logic [7:0] inj_data_b_1755007804603_822,
    input logic inj_in_p_1755007804601_428,
    input logic inj_in_q_1755007804601_617,
    input logic [1:0] inj_in_val_1755007804601_288,
    input logic [2:0] inj_in_val_1755007804605_118,
    input logic [31:0] inj_in_vec_1755007804602_778,
    input logic [4:0] inj_read_address_1755007804608_601,
    input bit inj_sel_1755007804613_319,
    input int inj_start_index_1755007804602_802,
    input logic [7:0] inj_start_val_i_1755007804601_21,
    input int inj_width_1755007804602_290,
    input logic [4:0] inj_write_address_1755007804608_24,
    input wire reset,
    output logic inj_dummy_out_1755007804609_361,
    output logic inj_o_bind_status_1755007804605_236,
    output logic [7:0] inj_out1_1755007804611_126,
    output logic [7:0] inj_out1_1755007804615_161,
    output logic inj_out2_1755007804611_815,
    output logic inj_out2_1755007804615_28,
    output logic inj_out_1755007804604_497,
    output logic [7:0] inj_out_1755007804606_790,
    output logic [7:0] inj_out_1755007804607_145,
    output logic inj_out_1755007804610_297,
    output logic [7:0] inj_out_data_1755007804609_995,
    output logic [7:0] inj_out_down_1755007804602_569,
    output logic inj_out_la_1755007804602_219,
    output logic inj_out_r_1755007804601_389,
    output logic [7:0] inj_out_reg_t_1755007804602_882,
    output reg inj_out_res_1755007804601_312,
    output reg inj_out_res_1755007804605_84,
    output logic [7:0] inj_out_up_1755007804602_515,
    output logic inj_out_valid_1755007804609_200,
    output logic [7:0] inj_read_data_1755007804608_880,
    output logic [7:0] inj_result1_1755007804603_45,
    output bit [7:0] inj_result1_1755007804613_348,
    output logic [7:0] inj_result2_1755007804603_7,
    output bit [7:0] inj_result2_1755007804613_879,
    output logic [15:0] inj_sum_out_i_1755007804601_564
);
    // BEGIN: case_default_ts1755007804601
    // BEGIN: split_for_loop_ts1755007804601
    // BEGIN: mod_large_array_target_ts1755007804602
    // BEGIN: split_if_empty_branches_ts1755007804602
    // BEGIN: range_select_indexed_packed_ts1755007804602
    // BEGIN: dup_cond_ts1755007804603
    // BEGIN: simple_and_gate_ts1755007804604
    // BEGIN: casez_xz_ts1755007804605
    // BEGIN: SynchronousMemory_ts1755007804608
    logic [7:0] mem_ts1755007804608 [0:31];
        // BEGIN: constant_sel_ts1755007804615
        assign inj_out1_1755007804615_161 = inj_in_vec_1755007804602_778[15:8];
        assign inj_out2_1755007804615_28 = inj_in_vec_1755007804602_778[3];
        // END: constant_sel_ts1755007804615

        // BEGIN: comb_conditional_ts1755007804614
        always @* begin
            if (inj_sel_1755007804613_319) begin
                inj_result1_1755007804613_348 = inj_data1_1755007804613_894;
                inj_result2_1755007804613_879 = inj_data1_1755007804613_894;
            end else begin
                inj_result1_1755007804613_348 = inj_data2_1755007804613_82;
                inj_result2_1755007804613_879 = inj_data2_1755007804613_82;
            end
        end
        // END: comb_conditional_ts1755007804614

        // BEGIN: constant_sel_ts1755007804611
        assign inj_out1_1755007804611_126 = inj_in_vec_1755007804602_778[15:8];
        assign inj_out2_1755007804611_815 = inj_in_vec_1755007804602_778[3];
        // END: constant_sel_ts1755007804611

        simple_xor_gate simple_xor_gate_inst_1755007804610_1505 (
            .out(inj_out_1755007804610_297),
            .in1(inj_in_p_1755007804601_428),
            .in2(inj_in_q_1755007804601_617)
        );
        // BEGIN: virtual_interface_lookup_mod_ts1755007804609
        always_comb begin
            inj_out_data_1755007804609_995  = inj_start_val_i_1755007804601_21;
            inj_out_valid_1755007804609_200 = inj_in_q_1755007804601_617;
            inj_dummy_out_1755007804609_361 = inj_in_p_1755007804601_428;
        end
        // END: virtual_interface_lookup_mod_ts1755007804609

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            inj_read_data_1755007804608_880 <= 8'h0;
        end else begin
            if (inj_in_q_1755007804601_617) begin
                mem_ts1755007804608[inj_write_address_1755007804608_24] <= inj_start_val_i_1755007804601_21;
            end
            inj_read_data_1755007804608_880 <= mem_ts1755007804608[inj_read_address_1755007804608_601];
        end
    end
    // END: SynchronousMemory_ts1755007804608

    timed_assign_unhandled timed_assign_unhandled_inst_1755007804607_7220 (
        .out(inj_out_1755007804607_145),
        .clk(clk),
        .in(inj_data_b_1755007804603_822)
    );
    sequential_always_assign sequential_always_assign_inst_1755007804606_3264 (
        .out(inj_out_1755007804606_790),
        .clk(clk),
        .in(inj_data_b_1755007804603_822)
    );
    module_to_bind module_to_bind_inst_1755007804605_3964 (
        .o_bind_status(inj_o_bind_status_1755007804605_236),
        .i_bind_clk(clk),
        .i_bind_control(inj_control_1755007804603_278)
    );
    always_comb begin
        inj_out_res_1755007804605_84 = 1'b0;
        casez (inj_in_val_1755007804605_118)
            3'b1??: inj_out_res_1755007804605_84 = 1'b1;
            3'b0z?: inj_out_res_1755007804605_84 = 1'b0;
            default: inj_out_res_1755007804605_84 = 1'b1;
        endcase
    end
    // END: casez_xz_ts1755007804605

    assign inj_out_1755007804604_497 = inj_in_q_1755007804601_617 & inj_in_p_1755007804601_428;
    // END: simple_and_gate_ts1755007804604

    always_comb begin
        inj_result1_1755007804603_45 = '0;
        inj_result2_1755007804603_7 = '0;
        if (inj_control_1755007804603_278[0]) begin
            inj_result1_1755007804603_45 = inj_start_val_i_1755007804601_21 + inj_data_b_1755007804603_822;
        end else begin
            inj_result1_1755007804603_45 = inj_start_val_i_1755007804601_21 - inj_data_b_1755007804603_822;
        end
        if (inj_control_1755007804603_278[1]) begin
            inj_result2_1755007804603_7 = inj_start_val_i_1755007804601_21 - inj_data_b_1755007804603_822;
        end else begin
            inj_result2_1755007804603_7 = inj_start_val_i_1755007804601_21 + inj_data_b_1755007804603_822;
        end
        case (inj_control_1755007804603_278[3:2])
            2'b00: inj_result1_1755007804603_45 = inj_start_val_i_1755007804601_21 & inj_data_b_1755007804603_822;
            2'b01: inj_result1_1755007804603_45 = inj_start_val_i_1755007804601_21 | inj_data_b_1755007804603_822;
            2'b10: inj_result2_1755007804603_7 = inj_start_val_i_1755007804601_21 & inj_data_b_1755007804603_822;
            2'b11: inj_result2_1755007804603_7 = inj_start_val_i_1755007804601_21 | inj_data_b_1755007804603_822;
            default: begin inj_result1_1755007804603_45 = '0; inj_result2_1755007804603_7 = '0; end
        endcase
        if (inj_control_1755007804603_278[0] == inj_control_1755007804603_278[1]) begin
            inj_result1_1755007804603_45 = inj_result1_1755007804603_45 + 1;
        end else if (inj_control_1755007804603_278[2] != inj_control_1755007804603_278[3]) begin
            inj_result2_1755007804603_7 = inj_result2_1755007804603_7 - 1;
        end
    end
    // END: dup_cond_ts1755007804603

    always_comb begin
        if (inj_start_index_1755007804602_802 >= 0 && inj_width_1755007804602_290 > 0 && inj_start_index_1755007804602_802 + inj_width_1755007804602_290 <= 32) begin
            case (inj_width_1755007804602_290)
                1: inj_out_up_1755007804602_515 = inj_in_vec_1755007804602_778[inj_start_index_1755007804602_802 +: 1];
                2: inj_out_up_1755007804602_515 = inj_in_vec_1755007804602_778[inj_start_index_1755007804602_802 +: 2];
                4: inj_out_up_1755007804602_515 = inj_in_vec_1755007804602_778[inj_start_index_1755007804602_802 +: 4];
                8: inj_out_up_1755007804602_515 = inj_in_vec_1755007804602_778[inj_start_index_1755007804602_802 +: 8];
                default: inj_out_up_1755007804602_515 = 'x;
            endcase
        end else begin
            inj_out_up_1755007804602_515 = 'x;
        end
        if (inj_start_index_1755007804602_802 >= inj_width_1755007804602_290 - 1 && inj_width_1755007804602_290 > 0 && inj_start_index_1755007804602_802 < 32) begin
            case (inj_width_1755007804602_290)
                1: inj_out_down_1755007804602_569 = inj_in_vec_1755007804602_778[inj_start_index_1755007804602_802 -: 1];
                2: inj_out_down_1755007804602_569 = inj_in_vec_1755007804602_778[inj_start_index_1755007804602_802 -: 2];
                4: inj_out_down_1755007804602_569 = inj_in_vec_1755007804602_778[inj_start_index_1755007804602_802 -: 4];
                8: inj_out_down_1755007804602_569 = inj_in_vec_1755007804602_778[inj_start_index_1755007804602_802 -: 8];
                default: inj_out_down_1755007804602_569 = 'x;
            endcase
        end else begin
            inj_out_down_1755007804602_569 = 'x;
        end
    end
    // END: range_select_indexed_packed_ts1755007804602

    always @(posedge clk) begin
        if (inj_in_p_1755007804601_428) begin
        end else begin
        end
    end
    // END: split_if_empty_branches_ts1755007804602

    assign inj_out_la_1755007804602_219 = inj_in_p_1755007804601_428;
    // END: mod_large_array_target_ts1755007804602

    LintSensitiveList LintSensitiveList_inst_1755007804601_9432 (
        .in_p(inj_in_p_1755007804601_428),
        .in_q(inj_in_q_1755007804601_617),
        .out_r(inj_out_r_1755007804601_389)
    );
    always @(posedge clk) begin
        inj_sum_out_i_1755007804601_564 <= 0;
        for (int i = 0; i < 4; i = i + 1) begin
            inj_sum_out_i_1755007804601_564 <= inj_sum_out_i_1755007804601_564 + inj_start_val_i_1755007804601_21 + i;
        end
    end
    // END: split_for_loop_ts1755007804601

    always_comb begin
        inj_out_res_1755007804601_312 = 1'b0;
        case (inj_in_val_1755007804601_288)
            2'b01: inj_out_res_1755007804601_312 = 1'b1;
            2'b10: inj_out_res_1755007804601_312 = 1'b0;
            default: inj_out_res_1755007804601_312 = 1'b1;
        endcase
    end
    // END: case_default_ts1755007804601
endmodule

