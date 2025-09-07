module snippet (
    input wire clk,
    input logic inj_a_1755007856862_409,
    input int inj_b_1755007856862_322,
    input wire reset,
    output logic inj_out_a_1755007856862_498,
    output int inj_out_b_1755007856862_269
);
    // BEGIN: ModuleBasic_ts1755007856862
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c_ts1755007856862;
    int   d_ts1755007856862;
    always_comb begin
        logic temp_v_ts1755007856862;
        temp_v_ts1755007856862 = d_ts1755007856862;
        c_ts1755007856862      = temp_v_ts1755007856862;
    end
    assign inj_out_a_1755007856862_498 = inj_a_1755007856862_409;
    assign d_ts1755007856862     = inj_b_1755007856862_322;
    assign inj_out_b_1755007856862_269 = d_ts1755007856862 + P1 + LP1;
    // END: ModuleBasic_ts1755007856862
endmodule

