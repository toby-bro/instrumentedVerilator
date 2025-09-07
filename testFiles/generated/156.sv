module LintSeqNonBlockAssign (
    input logic clk,
    input logic in_f,
    output logic out_g
);
    always_ff @(posedge clk) begin
        out_g <= in_f;
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

module snippet (
    input wire clk,
    input logic [7:0] inj_in_a_g_1755007805308_841,
    input logic [7:0] inj_in_b_g_1755007805308_639,
    input logic inj_in_f_1755007805308_724,
    input wire reset,
    output logic inj_out_c_1755007805308_205,
    output logic inj_out_g_1755007805308_138,
    output logic [7:0] inj_out_p_g_1755007805308_849,
    output logic [7:0] inj_out_q_g_1755007805308_514
);
    // BEGIN: mod_statement_block_var_ts1755007805309
    always_comb begin : block_with_vars
        int   block_local_int_ts1755007805309;
        logic [7:0] block_local_logic_ts1755007805309;
        block_local_int_ts1755007805309   = inj_in_f_1755007805308_724 ? 10 : 20;
        block_local_logic_ts1755007805309 = block_local_int_ts1755007805309;
        inj_out_c_1755007805308_205             = block_local_logic_ts1755007805309[0];
    end
    // END: mod_statement_block_var_ts1755007805309

    split_reorder_blocking split_reorder_blocking_inst_1755007805308_9197 (
        .in_a_g(inj_in_a_g_1755007805308_841),
        .in_b_g(inj_in_b_g_1755007805308_639),
        .out_p_g(inj_out_p_g_1755007805308_849),
        .out_q_g(inj_out_q_g_1755007805308_514)
    );
    LintSeqNonBlockAssign LintSeqNonBlockAssign_inst_1755007805308_3397 (
        .clk(clk),
        .in_f(inj_in_f_1755007805308_724),
        .out_g(inj_out_g_1755007805308_138)
    );
endmodule

