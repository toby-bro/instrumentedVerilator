module mixed_conn_child (
    input logic [7:0] data_in,
    input logic dummy_in,
    output logic dummy_out
);
    logic dummy_internal;
    always_comb dummy_internal = |data_in | dummy_in;
    assign dummy_out = dummy_internal;
endmodule

module snippet (
    input wire clk,
    input logic inj_control_signal_k_1755007909652_126,
    input bit [7:0] inj_data1_1755007909651_661,
    input bit [7:0] inj_data2_1755007909651_300,
    input logic [7:0] inj_data_in_k_1755007909652_345,
    input bit inj_sel_1755007909651_328,
    input wire reset,
    output logic [7:0] inj_data_out_k_1755007909652_896,
    output logic inj_dummy_out_1755007909652_600,
    output logic inj_o_result_1755007909653_70,
    output logic inj_reset_1755007909652_82,
    output bit [7:0] inj_result1_1755007909651_371,
    output bit [7:0] inj_result2_1755007909651_126
);
    // BEGIN: comb_conditional_ts1755007909651
    // BEGIN: split_input_only_var_ts1755007909652
    // BEGIN: cu_timeunit_mod_ts1755007909653
    logic internal_sig_ts1755007909653;
        // BEGIN: mod_simple_ref_ts1755007909653
        logic internal_sig_ts1755007909653;
        always_comb begin
            internal_sig_ts1755007909653 = internal_sig_ts1755007909653;
            inj_o_result_1755007909653_70 = internal_sig_ts1755007909653;
        end
        // END: mod_simple_ref_ts1755007909653

    always_ff @(posedge clk) begin
        inj_reset_1755007909652_82 <= 1'b0;
        internal_sig_ts1755007909653 = clk;
    end
    // END: cu_timeunit_mod_ts1755007909653

    mixed_conn_child mixed_conn_child_inst_1755007909652_5053 (
        .dummy_out(inj_dummy_out_1755007909652_600),
        .data_in(inj_data_in_k_1755007909652_345),
        .dummy_in(inj_control_signal_k_1755007909652_126)
    );
    always @(posedge clk) begin
        if (inj_control_signal_k_1755007909652_126) begin
            inj_data_out_k_1755007909652_896 <= inj_data_in_k_1755007909652_345;
        end
    end
    // END: split_input_only_var_ts1755007909652

    always @* begin
        if (inj_sel_1755007909651_328) begin
            inj_result1_1755007909651_371 = inj_data1_1755007909651_661;
            inj_result2_1755007909651_126 = inj_data1_1755007909651_661;
        end else begin
            inj_result1_1755007909651_371 = inj_data2_1755007909651_300;
            inj_result2_1755007909651_126 = inj_data2_1755007909651_300;
        end
    end
    // END: comb_conditional_ts1755007909651
endmodule

