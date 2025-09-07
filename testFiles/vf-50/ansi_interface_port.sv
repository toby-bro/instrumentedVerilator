module mod_casez_wildcard (
    input bit [3:0] in_mask_z,
    output bit [1:0] out_match_type_z
);
always_comb begin
    casez (in_mask_z)
        4'b10?0: begin
            out_match_type_z = 2'b00;
        end
        4'b011?: begin
            out_match_type_z = 2'b01;
        end
        default: begin
            out_match_type_z = 2'b11;
        end
    endcase
end
endmodule

module ansi_interface_port (
    input wire clk,
    input logic [3:0] inj_a_1755538446026_878,
    input logic [3:0] inj_b_1755538446026_963,
    input bit [3:0] inj_in_mask_z_1755538446026_836,
    input logic interface_input,
    input wire rst,
    output logic [7:0] inj_data_1755538446026_492,
    output bit [1:0] inj_out_match_type_z_1755538446026_903,
    output logic [3:0] inj_sum_1755538446026_794,
    output logic interface_output
);
    // BEGIN: child_concat_output_ts1755538446026
    // BEGIN: CombinationalLogicImplicit_ts1755538446026
    always @* begin
        inj_sum_1755538446026_794 = inj_a_1755538446026_878 + inj_b_1755538446026_963;
    end
    // END: CombinationalLogicImplicit_ts1755538446026

    mod_casez_wildcard mod_casez_wildcard_inst_1755538446026_4098 (
        .in_mask_z(inj_in_mask_z_1755538446026_836),
        .out_match_type_z(inj_out_match_type_z_1755538446026_903)
    );
    assign inj_data_1755538446026_492 = interface_input ? 8'hAA : 8'h55;
    // END: child_concat_output_ts1755538446026

    always_comb begin
        iface_port.signal_b = iface_port.signal_a;
        interface_output = interface_input;
    end
endmodule

