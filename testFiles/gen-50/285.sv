module snippet (
    input wire clk,
    input logic inj_a_1755007850532_798,
    input logic inj_b_1755007850532_510,
    input bit inj_enable_in_1755007850532_688,
    input wire reset,
    output bit inj_out_1755007850532_689,
    output logic inj_y_1755007850532_79
);
    // BEGIN: mod_comb_logic_ts1755007850532
    // BEGIN: mod_default_disable_ts1755007850532
    assign inj_out_1755007850532_689 = inj_enable_in_1755007850532_688;
    // END: mod_default_disable_ts1755007850532

    always_comb begin
        inj_y_1755007850532_79 = inj_a_1755007850532_798 & inj_b_1755007850532_510;
    end
    // END: mod_comb_logic_ts1755007850532
endmodule

