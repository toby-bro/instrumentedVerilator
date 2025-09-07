module mod_sub (
    input wire in_sub,
    output logic out_sub
);
    assign out_sub = in_sub;
endmodule

module snippet (
    input wire clk,
    input wire reset,
    output logic inj_out_sub_1755007916836_317
);
    mod_sub mod_sub_inst_1755007916836_4179 (
        .in_sub(clk),
        .out_sub(inj_out_sub_1755007916836_317)
    );
endmodule

