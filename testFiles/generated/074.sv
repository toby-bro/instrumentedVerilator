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
    input logic [31:0] inj_input1_1755007776766_263,
    input logic [7:0] inj_input2_byte_1755007776766_80,
    input wire reset,
    output logic inj_sequence_valid_1755007776766_472
);
    // BEGIN: module_sequence_different_if_ts1755007776767
    seq_if sif_port();
    seq2_if sif2_port();
    always_comb begin
        sif_port.value_a = inj_input1_1755007776766_263;
        sif2_port.status_byte = inj_input2_byte_1755007776766_80;
        inj_sequence_valid_1755007776766_472 = 1'b1;
    end
    // END: module_sequence_different_if_ts1755007776767
endmodule

