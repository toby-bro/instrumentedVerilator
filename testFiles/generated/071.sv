module snippet (
    input wire clk,
    input logic [7:0] inj_d1_1755007775680_5,
    input logic [7:0] inj_d2_1755007775680_313,
    input logic [7:0] inj_d3_1755007775680_488,
    input bit [7:0] inj_data1_1755007775679_403,
    input bit [7:0] inj_data2_1755007775679_403,
    input logic [3:0] inj_flags_1755007775680_947,
    input bit inj_sel_1755007775679_631,
    input wire reset,
    output logic [7:0] inj_out1_1755007775680_784,
    output bit [7:0] inj_result1_1755007775679_265,
    output bit [7:0] inj_result2_1755007775679_28
);
    // BEGIN: comb_conditional_ts1755007775679
    // BEGIN: dup_logic_ops_ts1755007775681
    logic cond1_ts1755007775680, cond2_ts1755007775680, cond3_ts1755007775680;
    logic complex_cond1_ts1755007775680, complex_cond2_ts1755007775680;
    assign cond1_ts1755007775680 = inj_flags_1755007775680_947[0] && inj_flags_1755007775680_947[1];
    assign cond2_ts1755007775680 = inj_flags_1755007775680_947[2] || inj_flags_1755007775680_947[3];
    assign cond3_ts1755007775680 = !inj_flags_1755007775680_947[0];
    assign complex_cond1_ts1755007775680 = (cond1_ts1755007775680 || cond2_ts1755007775680) && cond3_ts1755007775680;
    assign complex_cond2_ts1755007775680 = !(inj_flags_1755007775680_947[0] && inj_flags_1755007775680_947[1]) || (inj_flags_1755007775680_947[2] || !inj_flags_1755007775680_947[3]);
    always_comb begin
        inj_out1_1755007775680_784 = '0;
        if (complex_cond1_ts1755007775680) begin
            inj_out1_1755007775680_784 = inj_d1_1755007775680_5 + inj_d2_1755007775680_313;
        end else begin
            inj_out1_1755007775680_784 = inj_d1_1755007775680_5 ^ inj_d3_1755007775680_488;
        end
        if (complex_cond2_ts1755007775680) begin
            inj_out1_1755007775680_784 = inj_out1_1755007775680_784 + inj_d3_1755007775680_488;
        end else begin
            inj_out1_1755007775680_784 = inj_out1_1755007775680_784 - inj_d3_1755007775680_488;
        end
        if ((inj_flags_1755007775680_947[0] && inj_flags_1755007775680_947[1]) && (!inj_flags_1755007775680_947[2] || inj_flags_1755007775680_947[3])) begin
            inj_out1_1755007775680_784 = inj_out1_1755007775680_784 * 2;
        end
    end
    // END: dup_logic_ops_ts1755007775681

    always @* begin
        if (inj_sel_1755007775679_631) begin
            inj_result1_1755007775679_265 = inj_data1_1755007775679_403;
            inj_result2_1755007775679_28 = inj_data1_1755007775679_403;
        end else begin
            inj_result1_1755007775679_265 = inj_data2_1755007775679_403;
            inj_result2_1755007775679_28 = inj_data2_1755007775679_403;
        end
    end
    // END: comb_conditional_ts1755007775679
endmodule

