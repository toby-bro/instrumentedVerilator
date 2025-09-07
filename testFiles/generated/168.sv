module snippet (
    input wire clk,
    input logic [7:0] inj_i1_r_1755007809442_333,
    input logic [7:0] inj_i2_r_1755007809442_45,
    input logic [7:0] inj_i3_r_1755007809442_861,
    input wire reset,
    output logic [7:0] inj_o1_r_1755007809442_795,
    output logic [7:0] inj_o2_r_1755007809442_889,
    output logic [7:0] inj_o3_r_1755007809442_735
);
    // BEGIN: split_complex_blocking_ts1755007809443
    logic [7:0] t1_r_ts1755007809443, t2_r_ts1755007809443;
    always @(*) begin
        t1_r_ts1755007809443 = inj_i1_r_1755007809442_333 + inj_i2_r_1755007809442_45;
        inj_o1_r_1755007809442_795 = t1_r_ts1755007809443 - inj_i3_r_1755007809442_861;
        t2_r_ts1755007809443 = inj_i2_r_1755007809442_45 * inj_i3_r_1755007809442_861;
        inj_o2_r_1755007809442_889 = t1_r_ts1755007809443 + t2_r_ts1755007809443;
        inj_o3_r_1755007809442_735 = t2_r_ts1755007809443 / 2;
    end
    // END: split_complex_blocking_ts1755007809443
endmodule

