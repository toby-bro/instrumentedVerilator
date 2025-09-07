interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module MiscExpressions_ValueRange (
    input logic [15:0] in_vector,
    output logic [7:0] out_slice
);
    always_comb begin
        out_slice = in_vector[7:0];
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_data_case_a_1755007859762_899,
    input logic [7:0] inj_data_case_b_1755007859762_348,
    input logic [15:0] inj_in_vector_1755007859763_551,
    input logic [1:0] inj_select_case_1755007859762_439,
    input wire reset,
    output logic inj_case_output_ready_1755007859762_384,
    output logic [7:0] inj_out_slice_1755007859763_255
);
    // BEGIN: module_case_write_ts1755007859763
    MiscExpressions_ValueRange MiscExpressions_ValueRange_inst_1755007859763_9272 (
        .in_vector(inj_in_vector_1755007859763_551),
        .out_slice(inj_out_slice_1755007859763_255)
    );
    my_if case_vif_inst();
    always_comb begin
        case (inj_select_case_1755007859762_439)
            2'b00: begin
                case_vif_inst.data = 8'hAA;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b0;
            end
            2'b01: begin
                case_vif_inst.data = inj_data_case_a_1755007859762_899;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b1;
            end
            2'b10: begin
                case_vif_inst.data = inj_data_case_b_1755007859762_348;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b1;
            end
            default: begin
                case_vif_inst.data = 8'hFF;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b0;
            end
        endcase
        inj_case_output_ready_1755007859762_384 = case_vif_inst.ready;
    end
    // END: module_case_write_ts1755007859763
endmodule

