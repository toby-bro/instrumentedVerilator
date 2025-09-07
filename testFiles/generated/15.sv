module snippet (
    input wire clk,
    input logic [7:0] inj_data_in_1755004207981_899,
    input logic [1:0] inj_sel_1755004207981_19,
    input wire reset,
    output logic [7:0] inj_out_case_a_1755004207981_972,
    output logic [7:0] inj_out_case_b_1755004207981_828
);
    // BEGIN: mod_split_case_ts1755004207981
    logic [7:0]  split_case_var_ts1755004207981;
    logic [7:0] other_case_var_ts1755004207981;
    always_comb begin
        split_case_var_ts1755004207981 = 8'hFF;
        other_case_var_ts1755004207981 = 8'hAA;
        case (inj_sel_1755004207981_19)
            2'b00: begin
                split_case_var_ts1755004207981 = inj_data_in_1755004207981_899 + 5;
                other_case_var_ts1755004207981 = inj_data_in_1755004207981_899 + 6;
            end
            2'b01: begin
                split_case_var_ts1755004207981 = inj_data_in_1755004207981_899 - 5;
                other_case_var_ts1755004207981 = inj_data_in_1755004207981_899 - 6;
            end
            default: begin
                split_case_var_ts1755004207981 = inj_data_in_1755004207981_899;
                other_case_var_ts1755004207981 = inj_data_in_1755004207981_899;
            end
        endcase
        inj_out_case_a_1755004207981_972 = split_case_var_ts1755004207981;
        inj_out_case_b_1755004207981_828 = other_case_var_ts1755004207981;
    end
    // END: mod_split_case_ts1755004207981
endmodule

