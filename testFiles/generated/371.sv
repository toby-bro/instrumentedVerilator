module variable_sel_mux (
    input logic [7:0] in,
    input logic [2:0] index,
    output logic out
);
    assign out = in[index];
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_in_1755007878662_602,
    input logic [2:0] inj_index_1755007878662_981,
    input wire reset,
    output logic inj_out_1755007878662_922
);
    variable_sel_mux variable_sel_mux_inst_1755007878662_9480 (
        .out(inj_out_1755007878662_922),
        .in(inj_in_1755007878662_602),
        .index(inj_index_1755007878662_981)
    );
endmodule

