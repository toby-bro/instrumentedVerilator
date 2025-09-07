module snippet (
    input wire clk,
    input logic inj_i_attr_in_1755007888270_27,
    input wire reset,
    output logic inj_o_attr_out_1755007888270_919
);
    // BEGIN: attributes_test_ts1755007888270
    (* synthesis_preserve *) logic internal_signal;
    always_comb begin : my_combinational_block
        internal_signal = inj_i_attr_in_1755007888270_27 ? 1'b1 : 1'b0;
        inj_o_attr_out_1755007888270_919      = internal_signal;
    end
    // END: attributes_test_ts1755007888270
endmodule

