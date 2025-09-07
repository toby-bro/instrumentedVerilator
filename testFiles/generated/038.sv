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
    input logic [1:0] inj_in_val_1755007763585_136,
    input logic [31:0] inj_input1_1755007763585_154,
    input logic [7:0] inj_input2_byte_1755007763585_345,
    input wire reset,
    output reg inj_out_res_1755007763585_705,
    output logic inj_sequence_valid_1755007763585_432
);
    // BEGIN: case_single_default_after_item_ts1755007763585
    // BEGIN: module_sequence_different_if_ts1755007763585
    seq_if sif_port();
    seq2_if sif2_port();
    always_comb begin
        sif_port.value_a = inj_input1_1755007763585_154;
        sif2_port.status_byte = inj_input2_byte_1755007763585_345;
        inj_sequence_valid_1755007763585_432 = 1'b1;
    end
    // END: module_sequence_different_if_ts1755007763585

    always_comb begin
        inj_out_res_1755007763585_705 = 1'b0;
        case (inj_in_val_1755007763585_136)
            2'b01: inj_out_res_1755007763585_705 = 1'b1;
            default: inj_out_res_1755007763585_705 = 1'b0;
            2'b10: inj_out_res_1755007763585_705 = 1'b1;
        endcase
    end
    // END: case_single_default_after_item_ts1755007763585
endmodule

