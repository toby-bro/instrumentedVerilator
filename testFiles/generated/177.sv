module snippet (
    input wire clk,
    input logic [3:0] inj_v1_1755007812433_215,
    input logic [3:0] inj_v2_1755007812433_647,
    input wire reset,
    output logic inj_eq_1755007812433_771,
    output logic inj_o_done_ni_1755007812433_43
);
    // BEGIN: ModCompareVec_ts1755007812433
    // BEGIN: mod_no_inline_module_ts1755007812433
    logic r_toggle = 1'b0;
    always_ff @(posedge clk) begin
        r_toggle <= ~r_toggle;
    end
    assign inj_o_done_ni_1755007812433_43 = r_toggle;
    // END: mod_no_inline_module_ts1755007812433

    assign inj_eq_1755007812433_771 = (inj_v1_1755007812433_215 == inj_v2_1755007812433_647);
    // END: ModCompareVec_ts1755007812433
endmodule

