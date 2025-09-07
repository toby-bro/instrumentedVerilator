module child_concat_output (
    input logic dummy_in,
    output logic [7:0] data
);
    assign data = dummy_in ? 8'hAA : 8'h55;
endmodule

module snippet (
    input wire clk,
    input logic inj_dummy_in_1755007913693_647,
    input wire reset,
    output logic [7:0] inj_data_1755007913693_423
);
    child_concat_output child_concat_output_inst_1755007913693_1155 (
        .data(inj_data_1755007913693_423),
        .dummy_in(inj_dummy_in_1755007913693_647)
    );
endmodule

