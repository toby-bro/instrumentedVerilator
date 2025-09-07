module wide_ops_deep (
    input logic [63:0] wide_a,
    input logic [63:0] wide_b,
    input logic [63:0] wide_c,
    output logic [63:0] wide_out
);
    assign wide_out = (((wide_a + wide_b) ^ wide_c) & (~wide_a | wide_b)) + (wide_c >>> 5);
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_i1_s_1755007818006_175,
    input logic [7:0] inj_i2_s_1755007818006_858,
    input logic [7:0] inj_i3_s_1755007818006_845,
    input logic [63:0] inj_wide_a_1755007818007_442,
    input logic [63:0] inj_wide_b_1755007818007_953,
    input logic [63:0] inj_wide_c_1755007818007_643,
    input wire reset,
    output logic [7:0] inj_o1_s_1755007818006_800,
    output logic [7:0] inj_o2_s_1755007818006_243,
    output logic [7:0] inj_o3_s_1755007818006_649,
    output logic [63:0] inj_wide_out_1755007818007_810
);
    // BEGIN: split_complex_nb_ts1755007818007
    logic [7:0] t1_s_ts1755007818006, t2_s_ts1755007818006;
        wide_ops_deep wide_ops_deep_inst_1755007818007_1481 (
            .wide_a(inj_wide_a_1755007818007_442),
            .wide_b(inj_wide_b_1755007818007_953),
            .wide_c(inj_wide_c_1755007818007_643),
            .wide_out(inj_wide_out_1755007818007_810)
        );
    always @(posedge clk) begin
        t1_s_ts1755007818006 <= inj_i1_s_1755007818006_175 + inj_i2_s_1755007818006_858;
        inj_o1_s_1755007818006_800 <= t1_s_ts1755007818006 - inj_i3_s_1755007818006_845;
        t2_s_ts1755007818006 <= inj_i2_s_1755007818006_858 * inj_i3_s_1755007818006_845;
        inj_o2_s_1755007818006_243 <= t1_s_ts1755007818006 + t2_s_ts1755007818006;
        inj_o3_s_1755007818006_649 <= t2_s_ts1755007818006 / 2;
    end
    // END: split_complex_nb_ts1755007818007
endmodule

