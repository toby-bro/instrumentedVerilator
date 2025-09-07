module snippet (
    input wire clk,
    input logic [2:0] inj_in_val_1755007783934_600,
    input wire reset,
    output logic inj_out_md_1755007783934_308,
    output reg inj_out_res_1755007783934_710
);
    // BEGIN: casez_xz_alt_ts1755007783934
    // BEGIN: ModuleDefinition_ts1755007783934
    assign inj_out_md_1755007783934_308 = clk;
    // END: ModuleDefinition_ts1755007783934

    always_comb begin
        inj_out_res_1755007783934_710 = 1'b0;
        casez (inj_in_val_1755007783934_600)
            3'b1?z: inj_out_res_1755007783934_710 = 1'b1;
            3'b0z?: inj_out_res_1755007783934_710 = 1'b0;
            default: inj_out_res_1755007783934_710 = 1'b1;
        endcase
    end
    // END: casez_xz_alt_ts1755007783934
endmodule

