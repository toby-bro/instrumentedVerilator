module snippet (
    input wire clk,
    input bit inj_cfg_in_1755007846521_670,
    input logic inj_in1_1755007846521_150,
    input wire [7:0] inj_in1_1755007846521_396,
    input wire [7:0] inj_in2_1755007846521_587,
    input logic inj_in2_1755007846521_922,
    input wire reset,
    output bit inj_cfg_out_1755007846521_83,
    output wire [7:0] inj_out1_1755007846521_649,
    output wire [7:0] inj_out2_1755007846521_554,
    output logic inj_out_1755007846521_689
);
    // BEGIN: simple_xor_gate_ts1755007846521
    // BEGIN: Module_ConfigKeywords_ts1755007846521
    // BEGIN: multi_always_comb_ts1755007846521
    logic [7:0] intermediate1_ts1755007846521;
    logic [7:0] intermediate2_ts1755007846521;
    always @(*) begin
        intermediate1_ts1755007846521 = inj_in1_1755007846521_396 & inj_in2_1755007846521_587;
    end
    always @(*) begin
        intermediate2_ts1755007846521 = inj_in1_1755007846521_396 | inj_in2_1755007846521_587;
    end
    assign inj_out1_1755007846521_649 = intermediate1_ts1755007846521 + 8'd1;
    assign inj_out2_1755007846521_554 = intermediate2_ts1755007846521 - 8'd1;
    // END: multi_always_comb_ts1755007846521

    assign inj_cfg_out_1755007846521_83 = inj_cfg_in_1755007846521_670;
    // END: Module_ConfigKeywords_ts1755007846521

    assign inj_out_1755007846521_689 = inj_in1_1755007846521_150 ^ inj_in2_1755007846521_922;
    // END: simple_xor_gate_ts1755007846521
endmodule

