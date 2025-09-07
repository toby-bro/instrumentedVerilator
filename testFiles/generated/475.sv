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

module snippet #(
    parameter bit GEN = 1
) (
    input wire clk,
    input logic inj_condition_d_1755007913010_521,
    input wire [1:0] inj_dtl_action_sel_1755007913011_891,
    input wire [7:0] inj_dtl_data_a_1755007913011_904,
    input wire [7:0] inj_dtl_data_b_1755007913011_973,
    input logic [7:0] inj_in_false_d_1755007913010_485,
    input logic [7:0] inj_in_true_d_1755007913010_0,
    input logic [3:0] inj_val_a_1755007913011_118,
    input logic [3:0] inj_val_b_1755007913011_684,
    input logic inj_vif_valid_1755007913010_765,
    input wire reset,
    output logic [7:0] inj_dtl_result_reg_1755007913011_767,
    output logic inj_dummy_out_1755007913010_41,
    output logic inj_out_a_1755007913013_839,
    output logic [7:0] inj_out_data_1755007913010_946,
    output logic [7:0] inj_out_reg_d_1755007913010_447,
    output logic inj_out_valid_1755007913010_190,
    output logic [3:0] inj_result_1755007913011_707,
    output logic inj_sig_out_1755007913012_506
);
    // BEGIN: split_conditional_nb_ts1755007913010
    // BEGIN: virtual_interface_lookup_mod_ts1755007913010
    // BEGIN: CombinationalLogic_ts1755007913011
    // BEGIN: GenerateIfParam_ts1755007913012
    // BEGIN: mod_name_conflict_ts1755007913013
    logic conflict_var_ts1755007913013;
    parameter int conflict_param = 1;
    assign inj_out_a_1755007913013_839 = inj_condition_d_1755007913010_521;
    // END: mod_name_conflict_ts1755007913013

    generate
        if (GEN) begin : g_true
            assign inj_sig_out_1755007913012_506 = inj_condition_d_1755007913010_521;
        end
        else begin : g_false
            assign inj_sig_out_1755007913012_506 = ~inj_condition_d_1755007913010_521;
        end
    endgenerate
    // END: GenerateIfParam_ts1755007913012

    deep_task_logic deep_task_logic_inst_1755007913011_7552 (
        .dtl_rst_n(reset),
        .dtl_result_reg(inj_dtl_result_reg_1755007913011_767),
        .dtl_action_sel(inj_dtl_action_sel_1755007913011_891),
        .dtl_clk(clk),
        .dtl_data_a(inj_dtl_data_a_1755007913011_904),
        .dtl_data_b(inj_dtl_data_b_1755007913011_973),
        .dtl_en(clk)
    );
    always_comb begin
        if (inj_condition_d_1755007913010_521) begin
            inj_result_1755007913011_707 = inj_val_a_1755007913011_118 + inj_val_b_1755007913011_684;
        end else begin
            inj_result_1755007913011_707 = 4'h0;
        end
    end
    // END: CombinationalLogic_ts1755007913011

    always_comb begin
        inj_out_data_1755007913010_946  = inj_in_false_d_1755007913010_485;
        inj_out_valid_1755007913010_190 = inj_vif_valid_1755007913010_765;
        inj_dummy_out_1755007913010_41 = inj_condition_d_1755007913010_521;
    end
    // END: virtual_interface_lookup_mod_ts1755007913010

    always @(posedge clk) begin
        if (inj_condition_d_1755007913010_521) begin
            inj_out_reg_d_1755007913010_447 <= inj_in_true_d_1755007913010_0;
        end else begin
            inj_out_reg_d_1755007913010_447 <= inj_in_false_d_1755007913010_485;
        end
    end
    // END: split_conditional_nb_ts1755007913010
endmodule

