module snippet (
    input wire clk,
    input logic inj_in1_1755007807736_218,
    input wire reset,
    output logic [31:0] inj_out1_1755007807736_280
);
    // BEGIN: simple_macro_user_ts1755007807736
    `define SIMPLE_VALUE 32'd12345
    `define ANOTHER_SIMPLE (1 + 2)
    assign inj_out1_1755007807736_280 = inj_in1_1755007807736_218 ? (`SIMPLE_VALUE + `ANOTHER_SIMPLE) : 32'd0;
    // END: simple_macro_user_ts1755007807736
endmodule

