module reduction_ops (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic out
);
    assign out = &in1 | ^in2;
endmodule

module snippet (
    input wire clk,
    input logic inj_c1_x_1755007907610_18,
    input logic inj_c2_x_1755007907610_318,
    input logic inj_c3_x_1755007907610_289,
    input logic [7:0] inj_in1_f_1755007907609_738,
    input logic [7:0] inj_in2_f_1755007907609_552,
    input logic [7:0] inj_in3_f_1755007907609_55,
    input logic [7:0] inj_v4_x_1755007907610_363,
    input wire reset,
    output logic [7:0] inj_out1_f_1755007907609_340,
    output logic [7:0] inj_out2_f_1755007907609_6,
    output logic [7:0] inj_out3_f_1755007907609_702,
    output logic inj_out_1755007907609_83,
    output logic [7:0] inj_out_x_1755007907610_846
);
    // BEGIN: split_independent_nb_ts1755007907609
    // BEGIN: split_ifelse_chain_ts1755007907610
    always @(posedge clk) begin
        if (inj_c1_x_1755007907610_18) begin
            inj_out_x_1755007907610_846 <= inj_in3_f_1755007907609_55;
        end else if (inj_c2_x_1755007907610_318) begin
            inj_out_x_1755007907610_846 <= inj_in2_f_1755007907609_552;
        end else if (inj_c3_x_1755007907610_289) begin
            inj_out_x_1755007907610_846 <= inj_in1_f_1755007907609_738;
        end else begin
            inj_out_x_1755007907610_846 <= inj_v4_x_1755007907610_363;
        end
    end
    // END: split_ifelse_chain_ts1755007907610

    reduction_ops reduction_ops_inst_1755007907609_3168 (
        .in1(inj_in2_f_1755007907609_552),
        .in2(inj_in1_f_1755007907609_738),
        .out(inj_out_1755007907609_83)
    );
    always @(posedge clk) begin
        inj_out1_f_1755007907609_340 <= inj_in1_f_1755007907609_738;
        inj_out2_f_1755007907609_6 <= inj_in2_f_1755007907609_552;
        inj_out3_f_1755007907609_702 <= inj_in3_f_1755007907609_55;
    end
    // END: split_independent_nb_ts1755007907609
endmodule

