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

module deep_task_logic (
    input wire [1:0] dtl_action_sel,
    input wire dtl_clk,
    input wire [7:0] dtl_data_a,
    input wire [7:0] dtl_data_b,
    input wire dtl_en,
    input wire dtl_rst_n,
    output logic [7:0] dtl_result_reg
);
    task automatic perform_action;
        input [7:0] in_a;
        input [7:0] in_b;
        input [1:0] action;
        output logic [7:0] calculated_res;
        logic [7:0] temp_task_calc;
        if (action[0]) begin
            if (action[1]) begin
                temp_task_calc = in_a + in_b;
            end else begin
                temp_task_calc = in_a - in_b;
            end
        end else begin
            if (action[1]) begin
                temp_task_calc = in_a & in_b;
            end else begin
                temp_task_calc = in_a | in_b;
            end
        end
        case (temp_task_calc[1:0])
            2'b00: calculated_res = temp_task_calc ^ 8'hFF;
            2'b01: calculated_res = temp_task_calc + 1;
            2'b10: calculated_res = temp_task_calc - 1;
            default: calculated_res = temp_task_calc;
        endcase
    endtask
    always_ff @(posedge dtl_clk or negedge dtl_rst_n) begin
        if (!dtl_rst_n) begin
            dtl_result_reg <= 8'd0;
        end else begin
            logic [7:0] next_dtl_result;
            if (dtl_en) begin
                perform_action(dtl_data_a, dtl_data_b, dtl_action_sel, next_dtl_result);
            end else begin
                next_dtl_result = dtl_result_reg;
            end
            dtl_result_reg <= next_dtl_result;
        end
    end
endmodule

module macro_line_continuation_user (
    input logic lc_en,
    output logic [15:0] lc_val
);
    `define MULTI_VAL                \
        16'hABCD
    `define ADD_FIVE(v)              \
        ((v) +                         \
            5)
    logic [15:0] value_reg;
    always_comb begin
        if (lc_en)
            value_reg = `MULTI_VAL;
        else
            value_reg = `ADD_FIVE(16'h0010);
    end
    assign lc_val = value_reg;
endmodule

module named_block_logic (
    input logic i_gate,
    input logic i_in,
    output logic o_out
);
    logic r_internal;
    logic r_temp;
    always_comb begin : my_combinational_block
        r_temp = i_in & i_gate;
        r_internal = r_temp;
        o_out = r_internal;
    end
endmodule

module non_ansi_basic (
    non_ansi_a,
    non_ansi_basic_input,
    non_ansi_b,
    non_ansi_basic_output
);
    input wire non_ansi_a;
    output reg non_ansi_b;
    input logic non_ansi_basic_input;
    output logic non_ansi_basic_output;
    always_comb begin
        non_ansi_b = non_ansi_a;
        non_ansi_basic_output = non_ansi_basic_input;
    end
endmodule

module module_assignments_in_loops (
    input wire clk,
    input logic [2:0] in_shift,
    input logic [7:0] in_val,
    input wire [1:0] inj_dtl_action_sel_1755538414648_923,
    input wire [7:0] inj_dtl_data_a_1755538414648_724,
    input wire [7:0] inj_dtl_data_b_1755538414648_17,
    input wire [15:0] inj_i_packed_data_1755538414632_904,
    input logic inj_in1_bind_def_1755538414630_578,
    input logic inj_in_c_1755538414631_460,
    input int inj_val_in_1755538414639_171,
    input wire rst,
    output logic [7:0] inj_diff_v_1755538414634_430,
    output logic inj_dout_a_1755538414635_846,
    output logic inj_dout_b_1755538414635_535,
    output int inj_driven_var_1755538414639_404,
    output logic [7:0] inj_dtl_result_reg_1755538414648_215,
    output logic [15:0] inj_lc_val_1755538414646_770,
    output reg inj_non_ansi_b_1755538414631_46,
    output logic inj_non_ansi_basic_output_1755538414631_29,
    output logic [7:0] inj_o_member_sum_1755538414632_141,
    output logic inj_o_out_1755538414636_498,
    output logic inj_out1_bind_def_1755538414630_924,
    output logic [7:0] inj_out_diff_m2_1755538414651_236,
    output logic inj_out_e_1755538414631_886,
    output logic inj_out_single_1755538414638_961,
    output logic [7:0] inj_out_val_1755538414633_567,
    output logic [7:0] inj_out_val_o_1755538414644_962,
    output logic [7:0] inj_prod_v_1755538414634_260,
    output logic [7:0] inj_result_and_1755538414641_876,
    output logic [7:0] inj_result_or_1755538414641_554,
    output logic [7:0] inj_result_xor_1755538414641_154,
    output logic [7:0] inj_sum_v_1755538414634_768,
    output logic [7:0] inj_var_out_m2_1755538414651_29,
    output logic [3:0] out_part,
    output logic [7:0] out_reg
);
    localparam int PART_START = 4;
    localparam int PART_WIDTH = 4;
    logic [7:0] reg_var;
    logic [3:0] part_var;
        // BEGIN: ModuleGenerateIf_ts1755538414633
        parameter int PROCESS_ENABLE = 1;
        logic [7:0] processed_val_ts1755538414633;
            // BEGIN: m_driver_check_ts1755538414640
            int my_driven_var_ts1755538414640;
                // BEGIN: expr_postsub_comb_ts1755538414651
                logic [7:0] var_m2_ts1755538414651;
                always_comb begin
                    var_m2_ts1755538414651 = reg_var;
                    inj_out_diff_m2_1755538414651_236 = (var_m2_ts1755538414651--) - processed_val_ts1755538414633;
                    inj_var_out_m2_1755538414651_29 = var_m2_ts1755538414651;
                end
                // END: expr_postsub_comb_ts1755538414651

                deep_task_logic deep_task_logic_inst_1755538414648_6631 (
                    .dtl_clk(clk),
                    .dtl_data_a(inj_dtl_data_a_1755538414648_724),
                    .dtl_data_b(inj_dtl_data_b_1755538414648_17),
                    .dtl_en(rst),
                    .dtl_rst_n(rst),
                    .dtl_result_reg(inj_dtl_result_reg_1755538414648_215),
                    .dtl_action_sel(inj_dtl_action_sel_1755538414648_923)
                );
                macro_line_continuation_user macro_line_continuation_user_inst_1755538414646_6233 (
                    .lc_val(inj_lc_val_1755538414646_770),
                    .lc_en(inj_in1_bind_def_1755538414630_578)
                );
                // BEGIN: split_conditional_blocking_ts1755538414644
                always @(*) begin
                    if (inj_in1_bind_def_1755538414630_578) begin
                        inj_out_val_o_1755538414644_962 = reg_var;
                    end else begin
                        inj_out_val_o_1755538414644_962 = processed_val_ts1755538414633;
                    end
                end
                // END: split_conditional_blocking_ts1755538414644

                // BEGIN: BitwiseOperations_ts1755538414642
                assign inj_result_and_1755538414641_876 = in_val & processed_val_ts1755538414633;
                assign inj_result_or_1755538414641_554 = in_val | reg_var;
                assign inj_result_xor_1755538414641_154 = processed_val_ts1755538414633 ^ reg_var;
                // END: BitwiseOperations_ts1755538414642

            function automatic void write_to_var(input int val);
                my_driven_var_ts1755538414640 = val;
            endfunction
            always @(posedge clk) begin
                write_to_var(inj_val_in_1755538414639_171);
            end
            assign inj_driven_var_1755538414639_404 = my_driven_var_ts1755538414640;
            // END: m_driver_check_ts1755538414640

            // BEGIN: combinatorial_logic_ts1755538414638
            always_comb begin
                if (part_var > 4'd5) begin
                    inj_out_single_1755538414638_961 = 1'b1;
                end else begin
                    inj_out_single_1755538414638_961 = 1'b0;
                end
            end
            // END: combinatorial_logic_ts1755538414638

            named_block_logic named_block_logic_inst_1755538414636_4267 (
                .i_gate(inj_in1_bind_def_1755538414630_578),
                .i_in(inj_in_c_1755538414631_460),
                .o_out(inj_o_out_1755538414636_498)
            );
            ModMultipleAlways ModMultipleAlways_inst_1755538414635_7292 (
                .dout_a(inj_dout_a_1755538414635_846),
                .dout_b(inj_dout_b_1755538414635_535),
                .clk_a(clk),
                .clk_b(clk),
                .din_a(inj_in_c_1755538414631_460),
                .din_b(inj_in1_bind_def_1755538414630_578),
                .rst_n(rst)
            );
            // BEGIN: split_arith_nb_ts1755538414634
            always @(posedge clk) begin
                inj_sum_v_1755538414634_768 <= in_val + processed_val_ts1755538414633;
                inj_diff_v_1755538414634_430 <= in_val - processed_val_ts1755538414633;
                inj_prod_v_1755538414634_260 <= in_val * processed_val_ts1755538414633;
            end
            // END: split_arith_nb_ts1755538414634

        generate
            if (PROCESS_ENABLE) begin : process_block
                assign processed_val_ts1755538414633 = reg_var + 10;
            end else begin : bypass_block
                assign processed_val_ts1755538414633 = reg_var;
            end
        endgenerate
        assign inj_out_val_1755538414633_567 = processed_val_ts1755538414633;
        // END: ModuleGenerateIf_ts1755538414633

        // BEGIN: module_struct_ts1755538414632
        typedef struct packed {
            logic [3:0] part1_ts1755538414632;
            logic [7:0] part2_ts1755538414632;
            logic [3:0] part3_ts1755538414632;
        } my_packed_struct_t;
        my_packed_struct_t unpacked_data;
        assign unpacked_data = inj_i_packed_data_1755538414632_904;
        always @* begin
            inj_o_member_sum_1755538414632_141 = unpacked_data.part1_ts1755538414632 + unpacked_data.part2_ts1755538414632 + unpacked_data.part3_ts1755538414632;
        end
        // END: module_struct_ts1755538414632

        non_ansi_basic non_ansi_basic_inst_1755538414631_3994 (
            .non_ansi_a(clk),
            .non_ansi_b(inj_non_ansi_b_1755538414631_46),
            .non_ansi_basic_input(inj_in1_bind_def_1755538414630_578),
            .non_ansi_basic_output(inj_non_ansi_basic_output_1755538414631_29)
        );
        // BEGIN: LintCombBlockAssign_ts1755538414631
        always_comb begin
            inj_out_e_1755538414631_886 = inj_in_c_1755538414631_460 & inj_in1_bind_def_1755538414630_578;
        end
        // END: LintCombBlockAssign_ts1755538414631

        // BEGIN: mod_basic_bind_ts1755538414630
        assign inj_out1_bind_def_1755538414630_924 = ~inj_in1_bind_def_1755538414630_578;
        // END: mod_basic_bind_ts1755538414630

    always_comb begin
        reg_var  = in_val;
        part_var = 4'h0;
        for (int i = 0; i < 4; i++) begin
            reg_var  = reg_var + i;
            reg_var += (i * 2);
            reg_var <<= in_shift;
            reg_var[i % 8] = (reg_var[i % 8] == 1'b0);
            reg_var[PART_START +: PART_WIDTH] = i[3:0];
        end
        part_var = reg_var[7:4];
    end
    assign out_reg  = reg_var;
    assign out_part = part_var;
endmodule

