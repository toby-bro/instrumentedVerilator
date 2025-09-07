interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module BindSimpleModule (
    input bit in,
    output bit out
);
    assign out = in;
endmodule

module sequential_register (
    input logic clk,
    input logic data_in,
    input logic enable_in,
    input logic reset_n,
    output logic data_out
);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            data_out <= 1'b0; 
        end else if (enable_in) begin
            data_out <= data_in; 
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_a_1755007844102_513,
    input logic [3:0] inj_b_1755007844102_101,
    input bit inj_d_in_1755007844106_11,
    input logic inj_data_in_1755007844101_691,
    input logic inj_enable_in_1755007844101_786,
    input logic [7:0] inj_in_a_j_1755007844102_337,
    input logic [7:0] inj_in_b_j_1755007844102_409,
    input logic [1:0] inj_large_data_in_1755007844103_207,
    input wire reset,
    output bit inj_d_out_1755007844106_463,
    output logic inj_data_out_1755007844101_445,
    output logic [7:0] inj_large_sum_out_1755007844103_349,
    output logic inj_out1_1755007844103_572,
    output logic inj_out2_1755007844103_904,
    output logic inj_out_valid_status_1755007844106_964,
    output logic [7:0] inj_out_vec_y_1755007844102_72,
    output logic inj_out_wire_1755007844107_797,
    output logic [7:0] inj_out_x_j_1755007844102_25,
    output logic [7:0] inj_out_y_j_1755007844102_32,
    output logic [3:0] inj_sum_1755007844102_923
);
    // BEGIN: CombinationalLogicImplicit_ts1755007844102
    // BEGIN: split_multiple_in_branch_ts1755007844102
    // BEGIN: split_vector_assign_ts1755007844102
    // BEGIN: loop_unroll_limit_test_ts1755007844103
    logic [7:0] current_large_sum_ts1755007844103;
        // BEGIN: net_var_conn_child_ts1755007844107
        assign inj_out_wire_1755007844107_797 = inj_data_in_1755007844101_691;
        // END: net_var_conn_child_ts1755007844107

        // BEGIN: module_assign_blocking_ts1755007844106
        my_if vif_inst();
        always_comb begin
            vif_inst.data = current_large_sum_ts1755007844103;
            vif_inst.valid = 1'b1;
            vif_inst.ready = 1'b0;
            inj_out_valid_status_1755007844106_964 = vif_inst.valid;
        end
        // END: module_assign_blocking_ts1755007844106

        // BEGIN: DummyBindTarget_ts1755007844106
        assign inj_d_out_1755007844106_463 = inj_d_in_1755007844106_11;
        BindSimpleModule u_bind (.in(inj_d_in_1755007844106_11), .out());
        // END: DummyBindTarget_ts1755007844106

        // BEGIN: module_unpacked_array_ts1755007844104
        logic [1:0] data_ua[0:1] ;
        always_comb begin
            data_ua[0][0] = inj_enable_in_1755007844101_786;
            data_ua[0][1] = inj_data_in_1755007844101_691;
            data_ua[1][0] = data_ua[0][0];
            data_ua[1][1] = ~data_ua[0][1];
        end
        assign inj_out1_1755007844103_572 = data_ua[1][0];
        assign inj_out2_1755007844103_904 = data_ua[1][1];
        // END: module_unpacked_array_ts1755007844104

    always_comb begin
        current_large_sum_ts1755007844103 = 8'h00;
        for (int m = 0; m < 40; m = m + 1) begin 
            current_large_sum_ts1755007844103 = current_large_sum_ts1755007844103 + inj_large_data_in_1755007844103_207[0];
            current_large_sum_ts1755007844103 = current_large_sum_ts1755007844103 + inj_large_data_in_1755007844103_207[1];
            current_large_sum_ts1755007844103 = current_large_sum_ts1755007844103 + 1;
        end
        inj_large_sum_out_1755007844103_349 = current_large_sum_ts1755007844103;
    end
    // END: loop_unroll_limit_test_ts1755007844103

    always @(posedge clk) begin
        if (inj_enable_in_1755007844101_786) begin
            inj_out_vec_y_1755007844102_72[3:0] <= inj_in_a_j_1755007844102_337[3:0];
            inj_out_vec_y_1755007844102_72[7:4] <= inj_in_a_j_1755007844102_337[7:4] + 1;
        end else begin
            inj_out_vec_y_1755007844102_72 <= 8'hFF;
        end
    end
    // END: split_vector_assign_ts1755007844102

    always @(posedge clk) begin
        if (inj_enable_in_1755007844101_786) begin
            inj_out_x_j_1755007844102_25 <= inj_in_a_j_1755007844102_337 * 3;
            inj_out_y_j_1755007844102_32 <= inj_in_b_j_1755007844102_409 + 1;
        end else begin
            inj_out_x_j_1755007844102_25 <= inj_in_a_j_1755007844102_337;
            inj_out_y_j_1755007844102_32 <= inj_in_b_j_1755007844102_409;
        end
    end
    // END: split_multiple_in_branch_ts1755007844102

    always @* begin
        inj_sum_1755007844102_923 = inj_a_1755007844102_513 + inj_b_1755007844102_101;
    end
    // END: CombinationalLogicImplicit_ts1755007844102

    sequential_register sequential_register_inst_1755007844101_84 (
        .enable_in(inj_enable_in_1755007844101_786),
        .reset_n(reset),
        .data_out(inj_data_out_1755007844101_445),
        .clk(clk),
        .data_in(inj_data_in_1755007844101_691)
    );
endmodule

