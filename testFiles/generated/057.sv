module snippet (
    input wire clk,
    input logic [7:0] inj_d1_1755007770742_368,
    input logic [7:0] inj_d2_1755007770742_876,
    input logic [7:0] inj_d3_1755007770742_385,
    input logic [3:0] inj_flags_1755007770742_851,
    input wire reset,
    output logic [7:0] inj_out1_1755007770742_186
);
    // BEGIN: dup_logic_ops_ts1755007770743
    logic cond1_ts1755007770742, cond2_ts1755007770742, cond3_ts1755007770742;
    logic complex_cond1_ts1755007770742, complex_cond2_ts1755007770742;
    assign cond1_ts1755007770742 = inj_flags_1755007770742_851[0] && inj_flags_1755007770742_851[1];
    assign cond2_ts1755007770742 = inj_flags_1755007770742_851[2] || inj_flags_1755007770742_851[3];
    assign cond3_ts1755007770742 = !inj_flags_1755007770742_851[0];
    assign complex_cond1_ts1755007770742 = (cond1_ts1755007770742 || cond2_ts1755007770742) && cond3_ts1755007770742;
    assign complex_cond2_ts1755007770742 = !(inj_flags_1755007770742_851[0] && inj_flags_1755007770742_851[1]) || (inj_flags_1755007770742_851[2] || !inj_flags_1755007770742_851[3]);
    always_comb begin
        inj_out1_1755007770742_186 = '0;
        if (complex_cond1_ts1755007770742) begin
            inj_out1_1755007770742_186 = inj_d1_1755007770742_368 + inj_d2_1755007770742_876;
        end else begin
            inj_out1_1755007770742_186 = inj_d1_1755007770742_368 ^ inj_d3_1755007770742_385;
        end
        if (complex_cond2_ts1755007770742) begin
            inj_out1_1755007770742_186 = inj_out1_1755007770742_186 + inj_d3_1755007770742_385;
        end else begin
            inj_out1_1755007770742_186 = inj_out1_1755007770742_186 - inj_d3_1755007770742_385;
        end
        if ((inj_flags_1755007770742_851[0] && inj_flags_1755007770742_851[1]) && (!inj_flags_1755007770742_851[2] || inj_flags_1755007770742_851[3])) begin
            inj_out1_1755007770742_186 = inj_out1_1755007770742_186 * 2;
        end
    end
    // END: dup_logic_ops_ts1755007770743
endmodule

