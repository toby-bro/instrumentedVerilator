module snippet (
    input wire clk,
    input logic inj_i_p1_1755007815796_221,
    input logic inj_i_p2_1755007815796_647,
    input wire reset,
    output logic inj_o_p_and_1755007815796_639,
    output logic inj_o_p_xor_1755007815796_592
);
    // BEGIN: primitive_example_ts1755007815796
    and (inj_o_p_and_1755007815796_639, inj_i_p1_1755007815796_221, inj_i_p2_1755007815796_647);
    xor (inj_o_p_xor_1755007815796_592, inj_i_p1_1755007815796_221, inj_i_p2_1755007815796_647);
    // END: primitive_example_ts1755007815796
endmodule

