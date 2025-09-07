interface seq2_if;
    logic [7:0] status_byte;
    modport PortB (output status_byte);
endinterface
interface seq_if;
    logic [31:0] value_a;
    modport PortA (output value_a);
endinterface
module snippet (
    input wire clk,
    input logic inj_in_1755007841435_386,
    input logic [31:0] inj_input1_1755007841436_663,
    input logic [7:0] inj_input2_byte_1755007841436_142,
    input wire reset,
    output logic inj_out_1755007841435_532,
    output logic inj_sequence_valid_1755007841436_262
);
    // BEGIN: mod_always_event_ts1755007841435
    // BEGIN: module_sequence_different_if_ts1755007841436
    seq_if sif_port();
    seq2_if sif2_port();
    always_comb begin
        sif_port.value_a = inj_input1_1755007841436_663;
        sif2_port.status_byte = inj_input2_byte_1755007841436_142;
        inj_sequence_valid_1755007841436_262 = 1'b1;
    end
    // END: module_sequence_different_if_ts1755007841436

    always @(posedge clk or negedge reset) begin
        if (!reset) begin
            inj_out_1755007841435_532 <= 1'b0;
        end else begin
            inj_out_1755007841435_532 <= inj_in_1755007841435_386;
        end
    end
    // END: mod_always_event_ts1755007841435
endmodule

