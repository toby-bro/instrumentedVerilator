module snippet (
    input wire clk,
    input logic [7:0] inj_data_in_1755007777749_497,
    input logic inj_dummy_in_1755007777749_159,
    input wire reset,
    output logic inj_dummy_out_1755007777749_576
);
    // BEGIN: mixed_conn_child_ts1755007777749
    logic dummy_internal_ts1755007777749;
    always_comb dummy_internal_ts1755007777749 = |inj_data_in_1755007777749_497 | inj_dummy_in_1755007777749_159;
    assign inj_dummy_out_1755007777749_576 = dummy_internal_ts1755007777749;
    // END: mixed_conn_child_ts1755007777749
endmodule

