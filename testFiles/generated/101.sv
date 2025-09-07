module simple_xor_gate (
    input logic in1,
    input logic in2,
    output logic out
);
    assign out = in1 ^ in2;
endmodule

module snippet (
    input wire clk,
    input bit inj_enable_in_1755007786326_950,
    input logic inj_in1_1755007786325_560,
    input logic inj_in2_1755007786325_473,
    input bit [2:0] inj_in_state_case_1755007786325_40,
    input wire reset,
    output logic inj_out_1755007786325_763,
    output bit inj_out_1755007786326_252,
    output bit inj_out_priority_case_1755007786325_363,
    output bit inj_out_unique_case_1755007786325_144
);
    // BEGIN: mod_case_unique_priority_ts1755007786325
    // BEGIN: mod_default_disable_ts1755007786326
    assign inj_out_1755007786326_252 = inj_enable_in_1755007786326_950;
    // END: mod_default_disable_ts1755007786326

    simple_xor_gate simple_xor_gate_inst_1755007786325_8543 (
        .in1(inj_in1_1755007786325_560),
        .in2(inj_in2_1755007786325_473),
        .out(inj_out_1755007786325_763)
    );
always_comb begin
    inj_out_unique_case_1755007786325_144 = 1'b0;
    unique case (inj_in_state_case_1755007786325_40)
        3'd0: inj_out_unique_case_1755007786325_144 = 1'b0;
        3'd1: inj_out_unique_case_1755007786325_144 = 1'b1;
        3'd2: inj_out_unique_case_1755007786325_144 = 1'b0;
        3'd1: inj_out_unique_case_1755007786325_144 = 1'b1;
        default: inj_out_unique_case_1755007786325_144 = 1'b1;
    endcase
end
always_comb begin
    inj_out_priority_case_1755007786325_363 = 1'b0;
    priority case (inj_in_state_case_1755007786325_40)
        3'd0: inj_out_priority_case_1755007786325_363 = 1'b0;
        3'd1: inj_out_priority_case_1755007786325_363 = 1'b1;
        3'd2: inj_out_priority_case_1755007786325_363 = 1'b0;
        3'd1: inj_out_priority_case_1755007786325_363 = 1'b1;
        default: inj_out_priority_case_1755007786325_363 = 1'b1;
    endcase
end
    // END: mod_case_unique_priority_ts1755007786325
endmodule

