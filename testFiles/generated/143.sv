module constant_sel (
    input logic [31:0] in,
    output logic [7:0] out1,
    output logic out2
);
    assign out1 = in[15:8];
    assign out2 = in[3];
endmodule

module multiplexer_2to1 (
    input logic data0,
    input logic data1,
    input logic sel,
    output logic result
);
    assign result = sel ? data1 : data0;
endmodule

module procedural_complex (
    input logic [15:0] in1,
    input logic [15:0] in2,
    input logic sel,
    output logic [15:0] out1,
    output logic [15:0] out2
);
    logic [15:0] temp1;
    logic [15:0] temp2;
    always_comb begin
        temp1 = (in1 + in2) * 10;
        if (sel) begin
            temp2 = temp1 ^ (in1 >>> 2);
            out1 = temp2 & in2;
        end else begin
            temp2 = temp1 | (in2 <<< 3);
            out1 = temp2 + in1;
        end
        out2 = temp1 - temp2;
    end
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_a_1755007800826_329,
    input logic [3:0] inj_b_1755007800826_374,
    input logic [7:0] inj_in1_1755007800823_676,
    input logic [15:0] inj_in1_1755007800824_958,
    input logic [7:0] inj_in2_1755007800823_876,
    input logic [15:0] inj_in2_1755007800824_861,
    input logic [31:0] inj_in_1755007800825_322,
    input logic inj_sel_1755007800824_491,
    input logic inj_sel_1755007800826_699,
    input wire reset,
    output logic inj_o_sum_1755007800824_249,
    output logic [7:0] inj_out1_1755007800823_894,
    output logic [15:0] inj_out1_1755007800824_420,
    output logic [7:0] inj_out1_1755007800825_721,
    output logic [7:0] inj_out2_1755007800823_305,
    output logic [15:0] inj_out2_1755007800824_437,
    output logic inj_out2_1755007800825_286,
    output logic inj_result_1755007800826_53,
    output logic [3:0] inj_sum_1755007800826_853,
    output logic [7:0] inj_wide_reg_1755007800824_915
);
    // BEGIN: ModuleComb_ts1755007800824
    logic [7:0] internal_wire_ts1755007800824;
        // BEGIN: mod_lint_target_ts1755007800824
        logic l_reg_ts1755007800824;
            // BEGIN: CombinationalLogicImplicit_ts1755007800826
            always @* begin
                inj_sum_1755007800826_853 = inj_a_1755007800826_329 + inj_b_1755007800826_374;
            end
            // END: CombinationalLogicImplicit_ts1755007800826

            multiplexer_2to1 multiplexer_2to1_inst_1755007800826_8012 (
                .data0(inj_sel_1755007800824_491),
                .data1(l_reg_ts1755007800824),
                .sel(inj_sel_1755007800826_699),
                .result(inj_result_1755007800826_53)
            );
            constant_sel constant_sel_inst_1755007800825_8450 (
                .in(inj_in_1755007800825_322),
                .out1(inj_out1_1755007800825_721),
                .out2(inj_out2_1755007800825_286)
            );
        always_comb begin
            l_reg_ts1755007800824 = 1;
            inj_wide_reg_1755007800824_915 = {reset, clk};
        end
        assign inj_o_sum_1755007800824_249 = reset + clk;
        // END: mod_lint_target_ts1755007800824

        procedural_complex procedural_complex_inst_1755007800824_2862 (
            .in2(inj_in2_1755007800824_861),
            .sel(inj_sel_1755007800824_491),
            .out1(inj_out1_1755007800824_420),
            .out2(inj_out2_1755007800824_437),
            .in1(inj_in1_1755007800824_958)
        );
    assign internal_wire_ts1755007800824 = inj_in1_1755007800823_676 + inj_in2_1755007800823_876;
    always_comb begin
        if (internal_wire_ts1755007800824 > 8'd128) begin
            inj_out1_1755007800823_894 = internal_wire_ts1755007800824 - 1;
        end else begin
            inj_out1_1755007800823_894 = internal_wire_ts1755007800824 + 1;
        end
        inj_out2_1755007800823_305 = internal_wire_ts1755007800824 / 2;
    end
    // END: ModuleComb_ts1755007800824
endmodule

