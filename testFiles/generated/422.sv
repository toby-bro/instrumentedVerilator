module snippet (
    input wire clk,
    input logic inj_a_1755007895411_180,
    input int inj_b_1755007895411_403,
    input wire reset,
    output logic inj_out_a_1755007895411_122,
    output int inj_out_b_1755007895411_630
);
    // BEGIN: ModuleBasic_ts1755007895412
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c_ts1755007895412;
    int   d_ts1755007895412;
    always_comb begin
        logic temp_v_ts1755007895412;
        temp_v_ts1755007895412 = d_ts1755007895412;
        c_ts1755007895412      = temp_v_ts1755007895412;
    end
    assign inj_out_a_1755007895411_122 = inj_a_1755007895411_180;
    assign d_ts1755007895412     = inj_b_1755007895411_403;
    assign inj_out_b_1755007895411_630 = d_ts1755007895412 + P1 + LP1;
    // END: ModuleBasic_ts1755007895412
endmodule

