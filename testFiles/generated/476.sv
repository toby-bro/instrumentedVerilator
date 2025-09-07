module ReductionOperations (
    input logic [7:0] data_in,
    output logic and_reduce,
    output logic or_reduce,
    output logic xor_reduce
);
    assign and_reduce = &data_in;
    assign or_reduce = |data_in;
    assign xor_reduce = ^data_in;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_data_in_1755007913356_397,
    input wire reset,
    output logic inj_and_reduce_1755007913356_880,
    output logic inj_or_reduce_1755007913356_67,
    output logic inj_xor_reduce_1755007913356_338
);
    ReductionOperations ReductionOperations_inst_1755007913356_9310 (
        .data_in(inj_data_in_1755007913356_397),
        .and_reduce(inj_and_reduce_1755007913356_880),
        .or_reduce(inj_or_reduce_1755007913356_67),
        .xor_reduce(inj_xor_reduce_1755007913356_338)
    );
endmodule

