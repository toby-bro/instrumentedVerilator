module snippet (
    input wire clk,
    input logic inj_a_1755007855955_371,
    input int inj_b_1755007855955_796,
    input logic [7:0] inj_in1_1755007855956_632,
    input logic [7:0] inj_in2_1755007855956_103,
    input wire reset,
    output logic inj_out_1755007855956_560,
    output logic inj_out_a_1755007855955_863,
    output int inj_out_b_1755007855955_852
);
    // BEGIN: ModuleBasic_ts1755007855955
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c_ts1755007855955;
    int   d_ts1755007855955;
    always_comb begin
        logic temp_v_ts1755007855955;
            // BEGIN: reduction_ops_ts1755007855956
            assign inj_out_1755007855956_560 = &inj_in1_1755007855956_632 | ^inj_in2_1755007855956_103;
            // END: reduction_ops_ts1755007855956

        temp_v_ts1755007855955 = d_ts1755007855955;
        c_ts1755007855955      = temp_v_ts1755007855955;
    end
    assign inj_out_a_1755007855955_863 = inj_a_1755007855955_371;
    assign d_ts1755007855955     = inj_b_1755007855955_796;
    assign inj_out_b_1755007855955_852 = d_ts1755007855955 + P1 + LP1;
    // END: ModuleBasic_ts1755007855955
endmodule

