module snippet (
    input wire clk,
    input logic [7:0] inj_d1_1755007858367_140,
    input logic [7:0] inj_d2_1755007858367_467,
    input logic [7:0] inj_d3_1755007858367_754,
    input logic [3:0] inj_flags_1755007858367_459,
    input logic [15:0] inj_in_1755007858369_358,
    input wire reset,
    output logic [7:0] inj_out1_1755007858367_878,
    output logic [15:0] inj_out_1755007858369_304
);
    // BEGIN: dup_logic_ops_ts1755007858368
    logic cond1_ts1755007858368, cond2_ts1755007858368, cond3_ts1755007858368;
    logic complex_cond1_ts1755007858368, complex_cond2_ts1755007858368;
        // BEGIN: always_comb_assign_ts1755007858369
        always_comb begin
            inj_out_1755007858369_304 = inj_in_1755007858369_358;
        end
        // END: always_comb_assign_ts1755007858369

    assign cond1_ts1755007858368 = inj_flags_1755007858367_459[0] && inj_flags_1755007858367_459[1];
    assign cond2_ts1755007858368 = inj_flags_1755007858367_459[2] || inj_flags_1755007858367_459[3];
    assign cond3_ts1755007858368 = !inj_flags_1755007858367_459[0];
    assign complex_cond1_ts1755007858368 = (cond1_ts1755007858368 || cond2_ts1755007858368) && cond3_ts1755007858368;
    assign complex_cond2_ts1755007858368 = !(inj_flags_1755007858367_459[0] && inj_flags_1755007858367_459[1]) || (inj_flags_1755007858367_459[2] || !inj_flags_1755007858367_459[3]);
    always_comb begin
        inj_out1_1755007858367_878 = '0;
        if (complex_cond1_ts1755007858368) begin
            inj_out1_1755007858367_878 = inj_d1_1755007858367_140 + inj_d2_1755007858367_467;
        end else begin
            inj_out1_1755007858367_878 = inj_d1_1755007858367_140 ^ inj_d3_1755007858367_754;
        end
        if (complex_cond2_ts1755007858368) begin
            inj_out1_1755007858367_878 = inj_out1_1755007858367_878 + inj_d3_1755007858367_754;
        end else begin
            inj_out1_1755007858367_878 = inj_out1_1755007858367_878 - inj_d3_1755007858367_754;
        end
        if ((inj_flags_1755007858367_459[0] && inj_flags_1755007858367_459[1]) && (!inj_flags_1755007858367_459[2] || inj_flags_1755007858367_459[3])) begin
            inj_out1_1755007858367_878 = inj_out1_1755007858367_878 * 2;
        end
    end
    // END: dup_logic_ops_ts1755007858368
endmodule

