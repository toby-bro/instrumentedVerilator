module snippet (
    input wire clk,
    input int inj_in_val_1755007861299_170,
    input wire reset,
    output int inj_out_val_1755007861299_550
);
    // BEGIN: invalid_this_diag_mod_ts1755007861299
    assign inj_out_val_1755007861299_550 = inj_in_val_1755007861299_170;
    // END: invalid_this_diag_mod_ts1755007861299
endmodule

