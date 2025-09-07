module snippet (
    input wire clk,
    input logic [3:0] inj_in_vector_1755007848922_833,
    input wire reset,
    output logic inj_out_single_1755007848922_918
);
    // BEGIN: combinatorial_logic_ts1755007848922
    always_comb begin
        if (inj_in_vector_1755007848922_833 > 4'd5) begin
            inj_out_single_1755007848922_918 = 1'b1;
        end else begin
            inj_out_single_1755007848922_918 = 1'b0;
        end
    end
    // END: combinatorial_logic_ts1755007848922
endmodule

