module basic_assign_if (
    input logic in_a,
    input logic in_b,
    output logic out_c
);
    logic intermediate_wire;
    assign intermediate_wire = in_a & in_b;
    always_comb begin
        if (intermediate_wire) begin
            out_c = 1'b1;
        end else begin
            out_c = 1'b0;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_in_a_1755004217867_831,
    input logic inj_in_b_1755004217867_489,
    input wire reset,
    output logic inj_out_c_1755004217867_160
);
    basic_assign_if basic_assign_if_inst_1755004217867_6786 (
        .in_a(inj_in_a_1755004217867_831),
        .in_b(inj_in_b_1755004217867_489),
        .out_c(inj_out_c_1755004217867_160)
    );
endmodule

