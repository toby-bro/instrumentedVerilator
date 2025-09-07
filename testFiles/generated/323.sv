module snippet (
    input wire clk,
    input logic inj_i_data_in_1755007862830_613,
    input logic inj_i_write_en_1755007862830_304,
    input logic [7:0] inj_in_a_j_1755007862831_619,
    input logic [7:0] inj_in_b_j_1755007862831_621,
    input logic [2:0] inj_index_1755007862833_681,
    input wire reset,
    output logic inj_o_forceable_signal_1755007862830_890,
    output logic inj_o_read_signal_1755007862830_75,
    output logic inj_out_1755007862833_799,
    output logic [7:0] inj_out_x_j_1755007862831_139,
    output logic [7:0] inj_out_y_j_1755007862831_438
);
    // BEGIN: module_forceable_attr_ts1755007862830
    logic forceable_signal_ts1755007862830 ;
    logic read_internal_ts1755007862830;
        // BEGIN: variable_sel_mux_ts1755007862833
        assign inj_out_1755007862833_799 = inj_in_a_j_1755007862831_619[inj_index_1755007862833_681];
        // END: variable_sel_mux_ts1755007862833

        // BEGIN: split_multiple_in_branch_ts1755007862832
        always @(posedge clk) begin
            if (inj_i_data_in_1755007862830_613) begin
                inj_out_x_j_1755007862831_139 <= inj_in_a_j_1755007862831_619 * 3;
                inj_out_y_j_1755007862831_438 <= inj_in_b_j_1755007862831_621 + 1;
            end else begin
                inj_out_x_j_1755007862831_139 <= inj_in_a_j_1755007862831_619;
                inj_out_y_j_1755007862831_438 <= inj_in_b_j_1755007862831_621;
            end
        end
        // END: split_multiple_in_branch_ts1755007862832

    assign inj_o_forceable_signal_1755007862830_890 = forceable_signal_ts1755007862830;
    always @(posedge clk or negedge reset) begin
        if (!reset) begin
            forceable_signal_ts1755007862830 <= 1'b0;
            read_internal_ts1755007862830 <= 1'b0;
        end else begin
            if (inj_i_write_en_1755007862830_304) begin
                forceable_signal_ts1755007862830 <= inj_i_data_in_1755007862830_613;
            end
            read_internal_ts1755007862830 <= forceable_signal_ts1755007862830;
        end
    end
    assign inj_o_read_signal_1755007862830_75 = read_internal_ts1755007862830;
    // END: module_forceable_attr_ts1755007862830
endmodule

