module snippet #(
    parameter int WIDTH = 8
) (
    input wire clk,
    input logic [7:0] inj_din_1755007886268_104,
    input wire reset,
    output logic [7:0] inj_dout_1755007886268_430,
    output logic [7:0] inj_out_mv_a_1755007886268_526,
    output logic [7:0] inj_out_mv_b_1755007886268_632,
    output logic [7:0] inj_out_mv_c_1755007886268_907
);
    // BEGIN: Parameterized_ts1755007886268
    // BEGIN: mod_split_multiple_vars_ts1755007886269
    logic [7:0]  split_mv_var_ts1755007886269;
    logic [7:0] other_mv_var1_ts1755007886269;
    logic [7:0] other_mv_var2_ts1755007886269;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_mv_var_ts1755007886269 <= 8'b0;
            other_mv_var1_ts1755007886269 <= 8'b0;
            other_mv_var2_ts1755007886269 <= 8'b0;
        end else begin
            split_mv_var_ts1755007886269 <= inj_din_1755007886268_104;
            other_mv_var1_ts1755007886269 <= inj_din_1755007886268_104 + 1;
            other_mv_var2_ts1755007886269 <= inj_din_1755007886268_104 + 2;
            if (inj_din_1755007886268_104 > 100) begin
                split_mv_var_ts1755007886269 <= 8'hFF;
            end
            inj_out_mv_a_1755007886268_526 <= split_mv_var_ts1755007886269;
            inj_out_mv_b_1755007886268_632 <= other_mv_var1_ts1755007886269;
            inj_out_mv_c_1755007886268_907 <= other_mv_var2_ts1755007886269;
        end
    end
    // END: mod_split_multiple_vars_ts1755007886269

    assign inj_dout_1755007886268_430 = inj_din_1755007886268_104;
    // END: Parameterized_ts1755007886268
endmodule

