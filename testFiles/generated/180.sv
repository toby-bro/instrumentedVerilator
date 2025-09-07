module snippet (
    input wire clk,
    input logic [7:0] inj_data_in_1755007813473_652,
    input logic inj_in_a_1755007813472_698,
    input logic inj_in_b_1755007813472_741,
    input wire reset,
    output logic inj_dummy_out_1755007813473_589,
    output logic inj_out_c_1755007813472_61
);
    // BEGIN: basic_assign_if_ts1755007813473
    logic intermediate_wire_ts1755007813472;
        // BEGIN: mixed_conn_child_ts1755007813473
        logic dummy_internal_ts1755007813473;
        always_comb dummy_internal_ts1755007813473 = |inj_data_in_1755007813473_652 | inj_in_b_1755007813472_741;
        assign inj_dummy_out_1755007813473_589 = dummy_internal_ts1755007813473;
        // END: mixed_conn_child_ts1755007813473

    assign intermediate_wire_ts1755007813472 = inj_in_a_1755007813472_698 & inj_in_b_1755007813472_741;
    always_comb begin
        if (intermediate_wire_ts1755007813472) begin
            inj_out_c_1755007813472_61 = 1'b1;
        end else begin
            inj_out_c_1755007813472_61 = 1'b0;
        end
    end
    // END: basic_assign_if_ts1755007813473
endmodule

