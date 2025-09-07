interface struct_if;
    logic [7:0] packet_field1;
    logic [7:0] packet_field2;
    logic tx_en;
    modport Access (output packet_field1, output packet_field2, output tx_en);
endinterface
module mod_case_unique_priority (
    input bit [2:0] in_state_case,
    output bit out_priority_case,
    output bit out_unique_case
);
always_comb begin
    out_unique_case = 1'b0;
    unique case (in_state_case)
        3'd0: out_unique_case = 1'b0;
        3'd1: out_unique_case = 1'b1;
        3'd2: out_unique_case = 1'b0;
        3'd1: out_unique_case = 1'b1;
        default: out_unique_case = 1'b1;
    endcase
end
always_comb begin
    out_priority_case = 1'b0;
    priority case (in_state_case)
        3'd0: out_priority_case = 1'b0;
        3'd1: out_priority_case = 1'b1;
        3'd2: out_priority_case = 1'b0;
        3'd1: out_priority_case = 1'b1;
        default: out_priority_case = 1'b1;
    endcase
end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_in_field1_1755007774260_51,
    input logic [7:0] inj_in_field2_1755007774260_645,
    input bit [2:0] inj_in_state_case_1755007774260_741,
    input wire reset,
    output bit inj_out_priority_case_1755007774260_813,
    output bit inj_out_unique_case_1755007774260_100,
    output logic inj_tx_status_1755007774260_591
);
    // BEGIN: module_struct_write_ts1755007774260
    struct_if stif_inst();
    always_comb begin
        stif_inst.packet_field1 = inj_in_field1_1755007774260_51;
        stif_inst.packet_field2 = inj_in_field2_1755007774260_645;
        stif_inst.tx_en = 1'b1;
        inj_tx_status_1755007774260_591 = stif_inst.tx_en;
    end
    // END: module_struct_write_ts1755007774260

    mod_case_unique_priority mod_case_unique_priority_inst_1755007774260_1346 (
        .out_unique_case(inj_out_unique_case_1755007774260_100),
        .in_state_case(inj_in_state_case_1755007774260_741),
        .out_priority_case(inj_out_priority_case_1755007774260_813)
    );
endmodule

