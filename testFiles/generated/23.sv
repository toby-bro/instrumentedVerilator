module range_select_simple_packed (
    input logic [15:0] in_vec,
    output logic [7:0] out_slice_be,
    output logic [7:0] out_slice_le
);
    assign out_slice_be = in_vec[7:0]; 
    assign out_slice_le = in_vec[7:0]; 
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_in_val_a_l_1755004210769_765,
    input logic [7:0] inj_in_val_b_l_1755004210769_756,
    input logic [15:0] inj_in_vec_1755004210770_843,
    input wire reset,
    output logic [7:0] inj_out_slice_be_1755004210770_904,
    output logic [7:0] inj_out_slice_le_1755004210770_595,
    output logic [8:0] inj_out_val_c_l_1755004210769_549,
    output logic [7:0] inj_out_val_d_l_1755004210769_735
);
    // BEGIN: split_inputs_outputs_only_ts1755004210770
    range_select_simple_packed range_select_simple_packed_inst_1755004210770_8937 (
        .out_slice_be(inj_out_slice_be_1755004210770_904),
        .out_slice_le(inj_out_slice_le_1755004210770_595),
        .in_vec(inj_in_vec_1755004210770_843)
    );
    always @(*) begin
        inj_out_val_c_l_1755004210769_549 = inj_in_val_a_l_1755004210769_765 + inj_in_val_b_l_1755004210769_756;
        inj_out_val_d_l_1755004210769_735 = inj_in_val_a_l_1755004210769_765 - inj_in_val_b_l_1755004210769_756;
    end
    // END: split_inputs_outputs_only_ts1755004210770
endmodule

