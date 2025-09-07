module snippet (
    input wire clk,
    input logic [7:0] inj_in_val_1755007798861_442,
    input wire reset,
    output logic [7:0] inj_out_val_1755007798861_413
);
    // BEGIN: ModuleGenerateIf_ts1755007798862
    parameter int PROCESS_ENABLE = 1;
    logic [7:0] processed_val_ts1755007798861;
    generate
        if (PROCESS_ENABLE) begin : process_block
            assign processed_val_ts1755007798861 = inj_in_val_1755007798861_442 + 10;
        end else begin : bypass_block
            assign processed_val_ts1755007798861 = inj_in_val_1755007798861_442;
        end
    endgenerate
    assign inj_out_val_1755007798861_413 = processed_val_ts1755007798861;
    // END: ModuleGenerateIf_ts1755007798862
endmodule

