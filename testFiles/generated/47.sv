module combinatorial_logic (
    input logic [3:0] in_vector,
    output logic out_single
);
    always_comb begin
        if (in_vector > 4'd5) begin
            out_single = 1'b1;
        end else begin
            out_single = 1'b0;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_in_vector_1755004219367_23,
    input wire reset,
    output logic inj_out_single_1755004219367_722
);
    combinatorial_logic combinatorial_logic_inst_1755004219367_3492 (
        .out_single(inj_out_single_1755004219367_722),
        .in_vector(inj_in_vector_1755004219367_23)
    );
endmodule

