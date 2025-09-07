module snippet (
    input wire clk,
    input logic [7:0] inj_data_in_1755007845145_285,
    input logic inj_en_1755007845145_879,
    input wire reset,
    output logic [7:0] inj_data_out_1755007845145_117
);
    // BEGIN: sequential_register_en_ts1755007845145
    always_ff @(posedge clk) begin
        if (inj_en_1755007845145_879) begin
            inj_data_out_1755007845145_117 <= inj_data_in_1755007845145_285;
        end
    end
    // END: sequential_register_en_ts1755007845145
endmodule

