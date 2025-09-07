module snippet (
    input wire clk,
    input logic inj_i_gate_1755004206234_529,
    input logic inj_i_in_1755004206234_493,
    input wire reset,
    output logic inj_o_out_1755004206234_312
);
    // BEGIN: named_block_logic_ts1755004206234
    logic r_internal_ts1755004206234;
    logic r_temp_ts1755004206234;
    always_comb begin : my_combinational_block
        r_temp_ts1755004206234 = inj_i_in_1755004206234_493 & inj_i_gate_1755004206234_529;
        r_internal_ts1755004206234 = r_temp_ts1755004206234;
        inj_o_out_1755004206234_312 = r_internal_ts1755004206234;
    end
    // END: named_block_logic_ts1755004206234
endmodule

