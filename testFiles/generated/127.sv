module snippet (
    input wire clk,
    input logic signed [7:0] inj_data_1755007795540_595,
    input wire reset,
    output logic inj_out_valid_1755007795540_507
);
    // BEGIN: ModuleImplicitPort_ts1755007795540
    logic valid_ts1755007795540;
    assign valid_ts1755007795540 = |inj_data_1755007795540_595;
    assign inj_out_valid_1755007795540_507 = valid_ts1755007795540;
    // END: ModuleImplicitPort_ts1755007795540
endmodule

