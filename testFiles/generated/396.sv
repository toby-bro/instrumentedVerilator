module combinatorial_logic (
    input logic [3:0] in_vector,
    output logic out_single
);
    always_comb begin
        if (in_vector > 4'd5) begin
            out_single = 1'b1;
        end else begin
            out_single = 1'b0;
        end
    end
endmodule

module primitive_example (
    input logic i_p1,
    input logic i_p2,
    output logic o_p_and,
    output logic o_p_xor
);
    and (o_p_and, i_p1, i_p2);
    xor (o_p_xor, i_p1, i_p2);
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_byte_val_1755007886895_388,
    input logic inj_i_p1_1755007886896_278,
    input logic inj_i_p2_1755007886896_960,
    input logic [3:0] inj_in_vector_1755007886895_251,
    input logic [15:0] inj_packed_in_1755007886895_286,
    input wire reset,
    output logic [7:0] inj_byte_out_1755007886895_104,
    output logic inj_o_p_and_1755007886896_173,
    output logic inj_o_p_xor_1755007886896_299,
    output logic inj_out_single_1755007886895_694,
    output logic [15:0] inj_packed_out_1755007886895_612
);
    // BEGIN: PackedStructOps_ts1755007886895
    typedef struct packed {
        logic [7:0] low_ts1755007886895;
        logic [7:0] high_ts1755007886895;
    } pair_t;
    pair_t data_pair;
    primitive_example primitive_example_inst_1755007886896_5770 (
        .o_p_xor(inj_o_p_xor_1755007886896_299),
        .i_p1(inj_i_p1_1755007886896_278),
        .i_p2(inj_i_p2_1755007886896_960),
        .o_p_and(inj_o_p_and_1755007886896_173)
    );
    combinatorial_logic combinatorial_logic_inst_1755007886895_8498 (
        .out_single(inj_out_single_1755007886895_694),
        .in_vector(inj_in_vector_1755007886895_251)
    );
    assign data_pair.high_ts1755007886895 = inj_packed_in_1755007886895_286[15:8];
    assign data_pair.low_ts1755007886895 = inj_byte_val_1755007886895_388;
    assign inj_byte_out_1755007886895_104 = data_pair.high_ts1755007886895;
    assign inj_packed_out_1755007886895_612[15:8] = data_pair.high_ts1755007886895;
    assign inj_packed_out_1755007886895_612[7:0] = data_pair.low_ts1755007886895 + inj_byte_val_1755007886895_388;
    // END: PackedStructOps_ts1755007886895
endmodule

