module snippet (
    input wire clk,
    input wire [7:0] inj_in1_1755007873359_386,
    input wire [7:0] inj_in2_1755007873359_822,
    input wire reset,
    output wire [7:0] inj_out1_1755007873359_986,
    output wire [7:0] inj_out2_1755007873359_686,
    output logic inj_out_valid_1755007873359_559,
    output logic inj_reset_n_1755007873359_288
);
    // BEGIN: ansi_basic_ts1755007873359
    // BEGIN: multi_always_comb_ts1755007873359
    logic [7:0] intermediate1_ts1755007873359;
    logic [7:0] intermediate2_ts1755007873359;
        // BEGIN: ModuleImplicitPort_ts1755007873360
        logic valid_ts1755007873360;
        assign valid_ts1755007873360 = |intermediate1_ts1755007873359;
        assign inj_out_valid_1755007873359_559 = valid_ts1755007873360;
        // END: ModuleImplicitPort_ts1755007873360

    always @(*) begin
        intermediate1_ts1755007873359 = inj_in1_1755007873359_386 & inj_in2_1755007873359_822;
    end
    always @(*) begin
        intermediate2_ts1755007873359 = inj_in1_1755007873359_386 | inj_in2_1755007873359_822;
    end
    assign inj_out1_1755007873359_986 = intermediate1_ts1755007873359 + 8'd1;
    assign inj_out2_1755007873359_686 = intermediate2_ts1755007873359 - 8'd1;
    // END: multi_always_comb_ts1755007873359

    always_comb begin
        inj_reset_n_1755007873359_288 = clk;
    end
    // END: ansi_basic_ts1755007873359
endmodule

