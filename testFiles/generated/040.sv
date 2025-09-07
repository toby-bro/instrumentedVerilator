module snippet (
    input wire clk,
    input logic [7:0] inj_in_1755007764448_102,
    input wire reset,
    output logic [7:0] inj_out_1755007764448_996
);
    // BEGIN: timed_assign_unhandled_ts1755007764448
    always @(posedge clk) begin
        inj_out_1755007764448_996 <= inj_in_1755007764448_102;
    end
    // END: timed_assign_unhandled_ts1755007764448
endmodule

