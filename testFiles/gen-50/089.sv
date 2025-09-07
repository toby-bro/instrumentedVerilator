module DummyHierModule (
    input bit in_bit,
    output logic out_logic
);
    assign out_logic = in_bit;
endmodule

module snippet (
    input wire clk,
    input bit inj_in_bit_1755007782003_747,
    input wire reset,
    output logic inj_out_logic_1755007782003_25
);
    DummyHierModule DummyHierModule_inst_1755007782003_4514 (
        .out_logic(inj_out_logic_1755007782003_25),
        .in_bit(inj_in_bit_1755007782003_747)
    );
endmodule

