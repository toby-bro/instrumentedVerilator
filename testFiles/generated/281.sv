interface MyInterface (
    input logic clk
);
    logic req;
    logic valid;
    modport master (output req, input valid, input clk);
    modport slave (input req, output valid, input clk);
endinterface
module simple_assign (
    input logic [7:0] in,
    output logic [7:0] out
);
    assign out = in;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_in_1755007849233_510,
    input bit inj_in_h_1755007849233_981,
    input wire reset,
    output logic [7:0] inj_out_1755007849233_439,
    output logic inj_out_h_1755007849233_473,
    output logic inj_valid_out_1755007849233_343
);
    // BEGIN: CoverageHelper_ts1755007849233
    // BEGIN: ModuleWithInterface_ts1755007849233
    MyInterface my_if (clk);
    assign my_if.req = 1'b1;
    assign inj_valid_out_1755007849233_343 = my_if.valid;
    // END: ModuleWithInterface_ts1755007849233

    simple_assign simple_assign_inst_1755007849233_7872 (
        .out(inj_out_1755007849233_439),
        .in(inj_in_1755007849233_510)
    );
    assign inj_out_h_1755007849233_473 = inj_in_h_1755007849233_981;
    // END: CoverageHelper_ts1755007849233
endmodule

