interface simple_if (
    input logic clk
);
    logic data;
    logic ready;
    modport master (output data, input ready);
    modport slave (input data, output ready);
endinterface
module sub_module (
    input logic sub_in,
    output logic sub_out
);
    assign sub_out = !sub_in;
endmodule

module snippet (
    input wire clk,
    input logic inj_main_in_1755007816990_795,
    input wire reset,
    output logic inj_main_out_1755007816990_376
);
    // BEGIN: hierarchy_if_ts1755007816990
    sub_module u_sub (
        .sub_in(inj_main_in_1755007816990_795),
        .sub_out(inj_main_out_1755007816990_376)
    );
    simple_if if_inst (.clk(clk));
    always_comb begin
        if_inst.data = inj_main_in_1755007816990_795;
        if_inst.ready = inj_main_out_1755007816990_376;
    end
    // END: hierarchy_if_ts1755007816990
endmodule

