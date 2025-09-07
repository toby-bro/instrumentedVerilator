module snippet (
    input wire clk,
    input wire inj_g_in_1755007814541_575,
    input wire reset,
    output wire inj_g_out_and_1755007814541_262,
    output wire inj_g_out_or_1755007814541_272
);
    // BEGIN: Module_GatePrimitives_ts1755007814541
    and a1 (inj_g_out_and_1755007814541_262, inj_g_in_1755007814541_575, inj_g_in_1755007814541_575);
    or  o1 (inj_g_out_or_1755007814541_272 , inj_g_in_1755007814541_575, inj_g_in_1755007814541_575);
    // END: Module_GatePrimitives_ts1755007814541
endmodule

