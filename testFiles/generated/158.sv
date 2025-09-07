module snippet (
    input wire clk,
    input logic [3:0] inj_a_1755007806000_850,
    input logic [3:0] inj_b_1755007806000_97,
    input logic [7:0] inj_c_1755007806000_454,
    input wire reset,
    output logic [15:0] inj_out_concat_1755007806000_660
);
    // BEGIN: ConcatVectorOps_ts1755007806000
    assign inj_out_concat_1755007806000_660 = {inj_a_1755007806000_850, inj_b_1755007806000_97, inj_c_1755007806000_454};
    // END: ConcatVectorOps_ts1755007806000
endmodule

