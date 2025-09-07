module child_scalar_port (
    input logic data_in,
    output logic data_out
);
    assign data_out = data_in;
endmodule

module snippet (
    input wire clk,
    input logic inj_data_in_1755007869118_912,
    input logic [7:0] inj_i1_s_1755007869118_316,
    input logic [7:0] inj_i2_s_1755007869118_661,
    input logic [7:0] inj_i3_s_1755007869118_814,
    input wire reset,
    output logic inj_data_out_1755007869118_732,
    output logic [7:0] inj_o1_s_1755007869118_531,
    output logic [7:0] inj_o2_s_1755007869118_438,
    output logic [7:0] inj_o3_s_1755007869118_521,
    output logic [7:0] inj_out_vec_1755007869119_985
);
    // BEGIN: split_complex_nb_ts1755007869118
    logic [7:0] t1_s_ts1755007869118, t2_s_ts1755007869118;
        // BEGIN: SimpleLoopExample_ts1755007869119
        always_comb begin
            for (int i = 0; i < 8; i++) begin
                inj_out_vec_1755007869119_985[i] = inj_i2_s_1755007869118_661[7 - i];
            end
        end
        // END: SimpleLoopExample_ts1755007869119

        child_scalar_port child_scalar_port_inst_1755007869118_6706 (
            .data_in(inj_data_in_1755007869118_912),
            .data_out(inj_data_out_1755007869118_732)
        );
    always @(posedge clk) begin
        t1_s_ts1755007869118 <= inj_i1_s_1755007869118_316 + inj_i2_s_1755007869118_661;
        inj_o1_s_1755007869118_531 <= t1_s_ts1755007869118 - inj_i3_s_1755007869118_814;
        t2_s_ts1755007869118 <= inj_i2_s_1755007869118_661 * inj_i3_s_1755007869118_814;
        inj_o2_s_1755007869118_438 <= t1_s_ts1755007869118 + t2_s_ts1755007869118;
        inj_o3_s_1755007869118_521 <= t2_s_ts1755007869118 / 2;
    end
    // END: split_complex_nb_ts1755007869118
endmodule

