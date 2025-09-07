module ArrayIndexAndPartSelect (
    input logic [31:0] data_in,
    input int index_in,
    input logic [4:0] start_bit,
    output logic bit_out,
    output logic [7:0] byte_out
);
    logic [31:0] internal_data = data_in;
    assign bit_out = internal_data[index_in];
    assign byte_out = internal_data[start_bit +: 8];
endmodule

module snippet (
    input wire clk,
    input logic inj_condition_d_1755007886590_653,
    input logic [31:0] inj_data_in_1755007886590_522,
    input logic [7:0] inj_in_false_d_1755007886590_457,
    input logic [7:0] inj_in_true_d_1755007886590_111,
    input int inj_index_in_1755007886590_865,
    input logic [4:0] inj_start_bit_1755007886590_542,
    input wire reset,
    output logic inj_bit_out_1755007886590_186,
    output logic [7:0] inj_byte_out_1755007886590_893,
    output logic [7:0] inj_out_reg_d_1755007886590_251
);
    // BEGIN: split_conditional_nb_ts1755007886590
    always @(posedge clk) begin
        if (inj_condition_d_1755007886590_653) begin
            inj_out_reg_d_1755007886590_251 <= inj_in_true_d_1755007886590_111;
        end else begin
            inj_out_reg_d_1755007886590_251 <= inj_in_false_d_1755007886590_457;
        end
    end
    // END: split_conditional_nb_ts1755007886590

    ArrayIndexAndPartSelect ArrayIndexAndPartSelect_inst_1755007886590_6574 (
        .bit_out(inj_bit_out_1755007886590_186),
        .byte_out(inj_byte_out_1755007886590_893),
        .data_in(inj_data_in_1755007886590_522),
        .index_in(inj_index_in_1755007886590_865),
        .start_bit(inj_start_bit_1755007886590_542)
    );
endmodule

