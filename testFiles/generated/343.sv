module snippet (
    input wire clk,
    input logic [7:0] inj_in1_a_1755007869416_176,
    input bit inj_trigger_input_1755007869416_521,
    input wire reset,
    output logic [7:0] inj_out1_a_1755007869416_320,
    output bit inj_trigger_output_1755007869416_633
);
    // BEGIN: split_basic_blocking_ts1755007869416
    // BEGIN: PragmaOnceDirective_ts1755007869416
assign inj_trigger_output_1755007869416_633 = inj_trigger_input_1755007869416_521;
    // END: PragmaOnceDirective_ts1755007869416

    always @(*) begin
        inj_out1_a_1755007869416_320 = inj_in1_a_1755007869416_176;
    end
    // END: split_basic_blocking_ts1755007869416
endmodule

