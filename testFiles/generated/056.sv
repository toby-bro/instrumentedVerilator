module snippet (
    input wire clk,
    input bit [3:0] inj_in_mask_z_1755007770373_260,
    input wire reset,
    output bit [1:0] inj_out_match_type_z_1755007770373_47
);
    // BEGIN: mod_casez_wildcard_ts1755007770373
always_comb begin
    casez (inj_in_mask_z_1755007770373_260)
        4'b10?0: begin
            inj_out_match_type_z_1755007770373_47 = 2'b00;
        end
        4'b011?: begin
            inj_out_match_type_z_1755007770373_47 = 2'b01;
        end
        default: begin
            inj_out_match_type_z_1755007770373_47 = 2'b11;
        end
    endcase
end
    // END: mod_casez_wildcard_ts1755007770373
endmodule

