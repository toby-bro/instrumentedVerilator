module snippet (
    input wire clk,
    input logic [7:0] inj_in1_1755007865420_798,
    input logic [7:0] inj_in2_1755007865420_316,
    input wire reset,
    output logic [7:0] inj_out1_1755007865420_836,
    output logic [7:0] inj_out2_1755007865420_906
);
    // BEGIN: ModuleComb_ts1755007865421
    logic [7:0] internal_wire_ts1755007865421;
    assign internal_wire_ts1755007865421 = inj_in1_1755007865420_798 + inj_in2_1755007865420_316;
    always_comb begin
        if (internal_wire_ts1755007865421 > 8'd128) begin
            inj_out1_1755007865420_836 = internal_wire_ts1755007865421 - 1;
        end else begin
            inj_out1_1755007865420_836 = internal_wire_ts1755007865421 + 1;
        end
        inj_out2_1755007865420_906 = internal_wire_ts1755007865421 / 2;
    end
    // END: ModuleComb_ts1755007865421
endmodule

