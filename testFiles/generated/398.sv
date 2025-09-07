module snippet (
    input wire clk,
    input logic [15:0] inj_packed_in_1755007887620_521,
    input wire reset,
    output logic [7:0] inj_field0_byte_o_1755007887620_269
);
    // BEGIN: typedef_union_mod_ts1755007887621
    typedef union packed {
        logic [15:0] word_ts1755007887621;
        logic [1:0][7:0] byte_fields_ts1755007887621;
    } my_packed_union_t;
    my_packed_union_t my_union_var;
    always_comb begin
        my_union_var.word_ts1755007887621 = inj_packed_in_1755007887620_521;
    end
    assign inj_field0_byte_o_1755007887620_269 = my_union_var.byte_fields_ts1755007887621[0];
    // END: typedef_union_mod_ts1755007887621
endmodule

