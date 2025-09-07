module snippet (
    input wire clk,
    input int inj_data_in_1755007862228_371,
    input logic [7:0] inj_in_data_1755007862228_443,
    input wire reset,
    output int inj_data_out_1755007862228_440,
    output logic [7:0] inj_out_data_1755007862228_890
);
    // BEGIN: SimpleAssign_ts1755007862228
    // BEGIN: mod_named_begin_ts1755007862228
    always_comb begin : my_named_block
        inj_data_out_1755007862228_440 = inj_data_in_1755007862228_371;
    end
    // END: mod_named_begin_ts1755007862228

    assign inj_out_data_1755007862228_890 = inj_in_data_1755007862228_443;
    // END: SimpleAssign_ts1755007862228
endmodule

