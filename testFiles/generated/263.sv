module module_selection (
    input wire in_bit,
    input wire [2:0] in_index,
    input wire [1:0] in_part_lsb,
    input wire [7:0] in_vector,
    output logic out_bit_select,
    output logic [7:0] out_bitwise_ops,
    output logic [3:0] out_part_select,
    output logic [7:0] out_vector_assign
);
    always_comb begin
    out_vector_assign = in_vector;
    out_bit_select = in_vector[in_index];
    out_part_select = in_vector[in_part_lsb +: 4];
    out_bitwise_ops = in_vector & {8{in_bit}};
    end
endmodule

module snippet (
    input wire clk,
    input wire [2:0] inj_in_index_1755007842405_459,
    input wire [1:0] inj_in_part_lsb_1755007842405_937,
    input wire [7:0] inj_in_vector_1755007842405_185,
    input wire reset,
    output logic inj_out_bit_select_1755007842405_247,
    output logic [7:0] inj_out_bitwise_ops_1755007842405_724,
    output logic [3:0] inj_out_part_select_1755007842405_3,
    output logic [7:0] inj_out_vector_assign_1755007842405_885
);
    module_selection module_selection_inst_1755007842405_5223 (
        .out_part_select(inj_out_part_select_1755007842405_3),
        .out_vector_assign(inj_out_vector_assign_1755007842405_885),
        .in_bit(clk),
        .in_index(inj_in_index_1755007842405_459),
        .in_part_lsb(inj_in_part_lsb_1755007842405_937),
        .in_vector(inj_in_vector_1755007842405_185),
        .out_bit_select(inj_out_bit_select_1755007842405_247),
        .out_bitwise_ops(inj_out_bitwise_ops_1755007842405_724)
    );
endmodule

