module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_data_in_1755007910002_209,
    input logic [3:0] inj_i_bind_control_1755007910000_962,
    input logic [31:0] inj_in_vec_1755007910000_461,
    input int inj_start_index_1755007910000_146,
    input int inj_width_1755007910000_973,
    input wire reset,
    output logic inj_and_reduce_1755007910002_411,
    output logic inj_o_bind_status_1755007910000_962,
    output logic inj_or_reduce_1755007910002_531,
    output logic [7:0] inj_out1_1755007910003_970,
    output logic inj_out2_1755007910003_447,
    output logic [7:0] inj_out_down_1755007910000_970,
    output logic [7:0] inj_out_up_1755007910000_443,
    output logic inj_xor_reduce_1755007910002_750
);
    // BEGIN: range_select_indexed_packed_ts1755007910002
    // BEGIN: ReductionOperations_ts1755007910003
    // BEGIN: constant_sel_ts1755007910004
    assign inj_out1_1755007910003_970 = inj_in_vec_1755007910000_461[15:8];
    assign inj_out2_1755007910003_447 = inj_in_vec_1755007910000_461[3];
    // END: constant_sel_ts1755007910004

    assign inj_and_reduce_1755007910002_411 = &inj_data_in_1755007910002_209;
    assign inj_or_reduce_1755007910002_531 = |inj_data_in_1755007910002_209;
    assign inj_xor_reduce_1755007910002_750 = ^inj_data_in_1755007910002_209;
    // END: ReductionOperations_ts1755007910003

    always_comb begin
        if (inj_start_index_1755007910000_146 >= 0 && inj_width_1755007910000_973 > 0 && inj_start_index_1755007910000_146 + inj_width_1755007910000_973 <= 32) begin
            case (inj_width_1755007910000_973)
                1: inj_out_up_1755007910000_443 = inj_in_vec_1755007910000_461[inj_start_index_1755007910000_146 +: 1];
                2: inj_out_up_1755007910000_443 = inj_in_vec_1755007910000_461[inj_start_index_1755007910000_146 +: 2];
                4: inj_out_up_1755007910000_443 = inj_in_vec_1755007910000_461[inj_start_index_1755007910000_146 +: 4];
                8: inj_out_up_1755007910000_443 = inj_in_vec_1755007910000_461[inj_start_index_1755007910000_146 +: 8];
                default: inj_out_up_1755007910000_443 = 'x;
            endcase
        end else begin
            inj_out_up_1755007910000_443 = 'x;
        end
        if (inj_start_index_1755007910000_146 >= inj_width_1755007910000_973 - 1 && inj_width_1755007910000_973 > 0 && inj_start_index_1755007910000_146 < 32) begin
            case (inj_width_1755007910000_973)
                1: inj_out_down_1755007910000_970 = inj_in_vec_1755007910000_461[inj_start_index_1755007910000_146 -: 1];
                2: inj_out_down_1755007910000_970 = inj_in_vec_1755007910000_461[inj_start_index_1755007910000_146 -: 2];
                4: inj_out_down_1755007910000_970 = inj_in_vec_1755007910000_461[inj_start_index_1755007910000_146 -: 4];
                8: inj_out_down_1755007910000_970 = inj_in_vec_1755007910000_461[inj_start_index_1755007910000_146 -: 8];
                default: inj_out_down_1755007910000_970 = 'x;
            endcase
        end else begin
            inj_out_down_1755007910000_970 = 'x;
        end
    end
    // END: range_select_indexed_packed_ts1755007910002

    module_to_bind module_to_bind_inst_1755007910000_6948 (
        .o_bind_status(inj_o_bind_status_1755007910000_962),
        .i_bind_clk(clk),
        .i_bind_control(inj_i_bind_control_1755007910000_962)
    );
endmodule

