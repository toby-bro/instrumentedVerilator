module snippet (
    input wire clk,
    input logic inj_i_attr_in_1755007804233_87,
    input wire reset,
    output logic inj_o_attr_out_1755007804233_914,
    output logic inj_sub_out_1755007804233_26
);
    // BEGIN: attributes_test_ts1755007804233
    // BEGIN: sub_module_ts1755007804233
    assign inj_sub_out_1755007804233_26 = !inj_i_attr_in_1755007804233_87;
    // END: sub_module_ts1755007804233

    (* synthesis_preserve *) logic internal_signal;
    always_comb begin : my_combinational_block
        internal_signal = inj_i_attr_in_1755007804233_87 ? 1'b1 : 1'b0;
        inj_o_attr_out_1755007804233_914      = internal_signal;
    end
    // END: attributes_test_ts1755007804233
endmodule

