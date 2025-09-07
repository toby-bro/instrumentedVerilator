module keyword_import_export (
    input logic keyword_in,
    output logic keyword_out
);
    assign keyword_out = keyword_in;
endmodule

module snippet (
    input wire clk,
    input logic inj_keyword_in_1755007905911_569,
    input wire reset,
    output logic inj_keyword_out_1755007905911_799
);
    keyword_import_export keyword_import_export_inst_1755007905911_1960 (
        .keyword_in(inj_keyword_in_1755007905911_569),
        .keyword_out(inj_keyword_out_1755007905911_799)
    );
endmodule

