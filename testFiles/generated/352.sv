module snippet (
    input wire clk,
    input logic [31:0] inj_data_in_1755007872646_530,
    input int inj_index_in_1755007872646_396,
    input logic [4:0] inj_start_bit_1755007872646_96,
    input wire reset,
    output logic inj_bit_out_1755007872646_560,
    output logic [7:0] inj_byte_out_1755007872646_532
);
    // BEGIN: ArrayIndexAndPartSelect_ts1755007872647
    logic [31:0] internal_data = inj_data_in_1755007872646_530;
    assign inj_bit_out_1755007872646_560 = internal_data[inj_index_in_1755007872646_396];
    assign inj_byte_out_1755007872646_532 = internal_data[inj_start_bit_1755007872646_96 +: 8];
    // END: ArrayIndexAndPartSelect_ts1755007872647
endmodule

