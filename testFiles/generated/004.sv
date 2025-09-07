module snippet (
    input wire clk,
    input logic [3:0] inj_data_in_1755007751411_175,
    input wire reset,
    output logic [3:0] inj_data_out_1755007751411_810
);
    // BEGIN: GenerateFor_ts1755007751411
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : g_loop
            assign inj_data_out_1755007751411_810[i] = inj_data_in_1755007751411_175[i];
        end
    endgenerate
    // END: GenerateFor_ts1755007751411
endmodule

