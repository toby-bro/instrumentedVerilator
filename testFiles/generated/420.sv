module ComplexConversions (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic [15:0] out_concat
);
    always_comb begin
        out_concat = {in_a, in_b};
    end
endmodule

module typedef_struct_public_mod (
    input logic [15:0] packed_in,
    output logic [7:0] field2_o
);
    typedef struct packed {
        logic [7:0] field1;
        logic [7:0] field2;
    } my_public_packed_struct_t;
    my_public_packed_struct_t my_struct_var;
    always_comb begin
        my_struct_var = packed_in;
    end
    assign field2_o = my_struct_var.field2;
endmodule

module snippet (
    input wire clk,
    input logic inj_condition_h_1755007894736_365,
    input logic [7:0] inj_in_a_1755007894736_816,
    input logic [7:0] inj_in_b_1755007894736_217,
    input logic [15:0] inj_packed_in_1755007894736_942,
    input wire reset,
    output logic [7:0] inj_field2_o_1755007894736_547,
    output logic [15:0] inj_out_concat_1755007894736_488,
    output logic [7:0] inj_out_reg_h_1755007894736_514
);
    // BEGIN: split_if_only_then_ts1755007894736
    always @(posedge clk) begin
        if (inj_condition_h_1755007894736_365) begin
            inj_out_reg_h_1755007894736_514 <= inj_in_b_1755007894736_217;
        end
    end
    // END: split_if_only_then_ts1755007894736

    ComplexConversions ComplexConversions_inst_1755007894736_2062 (
        .in_a(inj_in_a_1755007894736_816),
        .in_b(inj_in_b_1755007894736_217),
        .out_concat(inj_out_concat_1755007894736_488)
    );
    typedef_struct_public_mod typedef_struct_public_mod_inst_1755007894736_6952 (
        .packed_in(inj_packed_in_1755007894736_942),
        .field2_o(inj_field2_o_1755007894736_547)
    );
endmodule

