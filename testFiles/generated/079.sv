module snippet (
    input wire clk,
    input logic inj_a_1755007778437_356,
    input logic inj_b_1755007778437_145,
    input wire [7:0] inj_in1_1755007778436_118,
    input wire [7:0] inj_in2_1755007778436_272,
    input wire reset,
    output wire [7:0] inj_out1_1755007778436_111,
    output wire [7:0] inj_out2_1755007778436_47,
    output logic inj_y_1755007778437_706
);
    // BEGIN: multi_always_comb_ts1755007778437
    logic [7:0] intermediate1_ts1755007778437;
    logic [7:0] intermediate2_ts1755007778437;
        // BEGIN: ModSimpleLogic_ts1755007778437
        assign inj_y_1755007778437_706 = inj_a_1755007778437_356 ^ inj_b_1755007778437_145;
        // END: ModSimpleLogic_ts1755007778437

    always @(*) begin
        intermediate1_ts1755007778437 = inj_in1_1755007778436_118 & inj_in2_1755007778436_272;
    end
    always @(*) begin
        intermediate2_ts1755007778437 = inj_in1_1755007778436_118 | inj_in2_1755007778436_272;
    end
    assign inj_out1_1755007778436_111 = intermediate1_ts1755007778437 + 8'd1;
    assign inj_out2_1755007778436_47 = intermediate2_ts1755007778437 - 8'd1;
    // END: multi_always_comb_ts1755007778437
endmodule

