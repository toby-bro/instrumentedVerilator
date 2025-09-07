module attributes_test (
    input logic i_attr_in,
    output logic o_attr_out
);
    (* synthesis_preserve *) logic internal_signal;
    always_comb begin : my_combinational_block
        internal_signal = i_attr_in ? 1'b1 : 1'b0;
        o_attr_out      = internal_signal;
    end
endmodule

module loop_unroll_limit_test (
    input logic [1:0] large_data_in,
    output logic [7:0] large_sum_out
);
    logic [7:0] current_large_sum;
    always_comb begin
        current_large_sum = 8'h00;
        for (int m = 0; m < 40; m = m + 1) begin 
            current_large_sum = current_large_sum + large_data_in[0];
            current_large_sum = current_large_sum + large_data_in[1];
            current_large_sum = current_large_sum + 1;
        end
        large_sum_out = current_large_sum;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_i_attr_in_1755007802241_655,
    input logic [2:0] inj_in_val_1755007802241_776,
    input logic [1:0] inj_large_data_in_1755007802241_249,
    input wire reset,
    output logic [7:0] inj_large_sum_out_1755007802241_18,
    output logic inj_o_attr_out_1755007802241_83,
    output reg inj_out_res_1755007802241_160
);
    // BEGIN: casez_xz_alt_ts1755007802241
    always_comb begin
        inj_out_res_1755007802241_160 = 1'b0;
        casez (inj_in_val_1755007802241_776)
            3'b1?z: inj_out_res_1755007802241_160 = 1'b1;
            3'b0z?: inj_out_res_1755007802241_160 = 1'b0;
            default: inj_out_res_1755007802241_160 = 1'b1;
        endcase
    end
    // END: casez_xz_alt_ts1755007802241

    attributes_test attributes_test_inst_1755007802241_665 (
        .i_attr_in(inj_i_attr_in_1755007802241_655),
        .o_attr_out(inj_o_attr_out_1755007802241_83)
    );
    loop_unroll_limit_test loop_unroll_limit_test_inst_1755007802241_2462 (
        .large_sum_out(inj_large_sum_out_1755007802241_18),
        .large_data_in(inj_large_data_in_1755007802241_249)
    );
endmodule

