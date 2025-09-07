module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module snippet (
    input wire clk,
    input logic inj_condition_o_1755007821854_389,
    input logic [7:0] inj_in_false_o_1755007821854_923,
    input logic [7:0] inj_in_true_o_1755007821854_243,
    input wire reset,
    output logic [7:0] inj_o_target_result_1755007821855_42,
    output logic [7:0] inj_out_val_o_1755007821854_714
);
    // BEGIN: split_conditional_blocking_ts1755007821855
    target_module_for_bind target_module_for_bind_inst_1755007821855_4920 (
        .i_target_data(inj_in_false_o_1755007821854_923),
        .o_target_result(inj_o_target_result_1755007821855_42),
        .i_target_clk(clk)
    );
    always @(*) begin
        if (inj_condition_o_1755007821854_389) begin
            inj_out_val_o_1755007821854_714 = inj_in_true_o_1755007821854_243;
        end else begin
            inj_out_val_o_1755007821854_714 = inj_in_false_o_1755007821854_923;
        end
    end
    // END: split_conditional_blocking_ts1755007821855
endmodule

