module snippet (
    input wire clk,
    input wire [7:0] inj_in_array_data_1755004215303_607,
    input wire [1:0] inj_select_idx_1755004215304_494,
    input wire reset,
    output wire [3:0] inj_out_element_1755004215304_670
);
    // BEGIN: unpacked_array_module_ts1755004215304
    logic [3:0] data_array_ts1755004215304 [4];
    always @(*) begin
        data_array_ts1755004215304[0] = inj_in_array_data_1755004215303_607[3:0];
        data_array_ts1755004215304[1] = inj_in_array_data_1755004215303_607[7:4];
        data_array_ts1755004215304[2] = 4'd8;
        data_array_ts1755004215304[3] = 4'd12;
    end
    assign inj_out_element_1755004215304_670 = data_array_ts1755004215304[inj_select_idx_1755004215304_494];
    // END: unpacked_array_module_ts1755004215304
endmodule

