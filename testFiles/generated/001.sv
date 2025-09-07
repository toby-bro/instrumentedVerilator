module snippet (
    input wire clk,
    input logic signed [7:0] inj_data_1755007750388_576,
    input wire reset,
    output logic inj_out_valid_1755007750388_636
);
    // BEGIN: ModuleImplicitPort_ts1755007750388
    logic valid_ts1755007750388;
    assign valid_ts1755007750388 = |inj_data_1755007750388_576;
    assign inj_out_valid_1755007750388_636 = valid_ts1755007750388;
    // END: ModuleImplicitPort_ts1755007750388
endmodule

