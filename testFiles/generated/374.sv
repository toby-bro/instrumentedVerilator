module multi_always_comb (
    input wire [7:0] in1,
    input wire [7:0] in2,
    output wire [7:0] out1,
    output wire [7:0] out2
);
    logic [7:0] intermediate1;
    logic [7:0] intermediate2;
    always @(*) begin
        intermediate1 = in1 & in2;
    end
    always @(*) begin
        intermediate2 = in1 | in2;
    end
    assign out1 = intermediate1 + 8'd1;
    assign out2 = intermediate2 - 8'd1;
endmodule

module snippet (
    input wire clk,
    input wire [7:0] inj_in1_1755007879665_765,
    input wire [7:0] inj_in2_1755007879665_43,
    input logic inj_in_a_1755007879665_829,
    input wire reset,
    output wire [7:0] inj_out1_1755007879665_109,
    output wire [7:0] inj_out2_1755007879665_891,
    output logic inj_out_a_1755007879665_912
);
    // BEGIN: mod_name_conflict_ts1755007879665
    logic conflict_var_ts1755007879665;
    parameter int conflict_param = 1;
    assign inj_out_a_1755007879665_912 = inj_in_a_1755007879665_829;
    // END: mod_name_conflict_ts1755007879665

    multi_always_comb multi_always_comb_inst_1755007879665_8418 (
        .out1(inj_out1_1755007879665_109),
        .out2(inj_out2_1755007879665_891),
        .in1(inj_in1_1755007879665_765),
        .in2(inj_in2_1755007879665_43)
    );
endmodule

