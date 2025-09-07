module snippet (
    input wire clk,
    input logic [3:0] inj_a_1755004211420_172,
    input logic [3:0] inj_b_1755004211420_823,
    input logic [7:0] inj_c_1755004211420_391,
    input wire reset,
    output logic [15:0] inj_out_concat_1755004211420_586
);
    // BEGIN: ConcatVectorOps_ts1755004211420
    assign inj_out_concat_1755004211420_586 = {inj_a_1755004211420_172, inj_b_1755004211420_823, inj_c_1755004211420_391};
    // END: ConcatVectorOps_ts1755004211420
endmodule

