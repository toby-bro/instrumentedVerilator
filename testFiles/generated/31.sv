module mismatched_width_unhandled (
    input logic [7:0] in,
    output logic [3:0] out
);
    assign out = in;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_in_1755004213523_409,
    input bit inj_in_bit_1755004213523_362,
    input logic inj_in_data_1755004213522_170,
    input wire [7:0] inj_in_val1_1755004213523_514,
    input wire [7:0] inj_in_val2_1755004213523_918,
    input wire reset,
    output logic inj_concat_port_output_1755004213522_678,
    output logic [1:0] inj_non_ansi_i_1755004213522_947,
    output logic [1:0] inj_non_ansi_j_1755004213522_90,
    output logic [3:0] inj_out_1755004213523_21,
    output logic inj_out_data_pull0_1755004213522_742,
    output logic inj_out_data_pull1_1755004213522_649,
    output logic inj_out_logic_1755004213523_527,
    output logic [3:0] inj_out_narrow_1755004213523_937,
    output logic [7:0] inj_out_ternary_result_1755004213523_160,
    output logic inj_out_wire_1755004213522_969
);
    // BEGIN: module_with_unconnected_drive_ts1755004213522
    // BEGIN: non_ansi_concat_port_ts1755004213522
    output logic [1:0] inj_non_ansi_i_1755004213522_947_ts1755004213522;
    output logic [1:0] inj_non_ansi_j_1755004213522_90_ts1755004213522;
    input logic inj_in_data_1755004213522_170_ts1755004213522;
    output logic inj_concat_port_output_1755004213522_678_ts1755004213522;
        // BEGIN: module_ternary_ts1755004213523
        always_comb begin
        inj_out_ternary_result_1755004213523_160 = clk ? inj_in_val1_1755004213523_514 : inj_in_val2_1755004213523_918;
        end
        // END: module_ternary_ts1755004213523

        // BEGIN: LintImplicitWidth_ts1755004213523
        assign inj_out_narrow_1755004213523_937 = inj_in_1755004213523_409;
        // END: LintImplicitWidth_ts1755004213523

        // BEGIN: DummyHierModule_ts1755004213523
        assign inj_out_logic_1755004213523_527 = inj_in_bit_1755004213523_362;
        // END: DummyHierModule_ts1755004213523

        mismatched_width_unhandled mismatched_width_unhandled_inst_1755004213523_1430 (
            .in(inj_in_1755004213523_409),
            .out(inj_out_1755004213523_21)
        );
        // BEGIN: net_var_conn_child_ts1755004213522
        assign inj_out_wire_1755004213522_969 = inj_concat_port_output_1755004213522_678_ts1755004213522;
        // END: net_var_conn_child_ts1755004213522

    assign inj_non_ansi_i_1755004213522_947_ts1755004213522 = 2'b10;
    assign inj_non_ansi_j_1755004213522_90_ts1755004213522 = 2'b01;
    assign inj_concat_port_output_1755004213522_678_ts1755004213522 = inj_in_data_1755004213522_170_ts1755004213522;
    // END: non_ansi_concat_port_ts1755004213522

    assign inj_out_data_pull1_1755004213522_649 = inj_in_data_1755004213522_170;
    assign inj_out_data_pull0_1755004213522_742 = ~inj_in_data_1755004213522_170;
    // END: module_with_unconnected_drive_ts1755004213522
endmodule

