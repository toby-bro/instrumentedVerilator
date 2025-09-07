module snippet (
    input wire clk,
    input logic inj_cond1_1755004212823_101,
    input logic inj_cond2_1755004212823_992,
    input logic [7:0] inj_data_in_1755004212823_781,
    input wire reset,
    output logic inj_bind_out_1755004212826_365,
    output wire inj_out_1755004212824_571,
    output logic [7:0] inj_out_nested_a_1755004212823_555,
    output logic [7:0] inj_out_nested_b_1755004212823_698,
    output logic inj_udnt_output_1755004212825_758,
    output logic inj_uout_1755004212825_490
);
    // BEGIN: mod_split_nested_ts1755004212824
    logic [7:0]  split_nested_var_ts1755004212824;
    logic [7:0] other_nested_var_ts1755004212824;
        // BEGIN: bind_module_ts1755004212826
        assign inj_bind_out_1755004212826_365 = inj_cond1_1755004212823_101;
        // END: bind_module_ts1755004212826

        // BEGIN: udnt_port_module_ts1755004212825
        assign inj_uout_1755004212825_490 = inj_cond2_1755004212823_992;
        assign inj_udnt_output_1755004212825_758 = inj_cond1_1755004212823_101;
        // END: udnt_port_module_ts1755004212825

        // BEGIN: mod_simple_ts1755004212824
        assign inj_out_1755004212824_571 = reset;
        // END: mod_simple_ts1755004212824

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_nested_var_ts1755004212824 <= 8'b0;
            other_nested_var_ts1755004212824 <= 8'b0;
        end else begin
            split_nested_var_ts1755004212824 <= 8'h11; 
            other_nested_var_ts1755004212824 <= 8'h22; 
            if (inj_cond1_1755004212823_101) begin
                split_nested_var_ts1755004212824 <= inj_data_in_1755004212823_781 + 10;
                other_nested_var_ts1755004212824 <= inj_data_in_1755004212823_781 + 20;
                if (inj_cond2_1755004212823_992) begin
                    split_nested_var_ts1755004212824 <= inj_data_in_1755004212823_781 + 100;
                    other_nested_var_ts1755004212824 <= inj_data_in_1755004212823_781 + 200;
                end
            end else begin
                split_nested_var_ts1755004212824 <= inj_data_in_1755004212823_781 - 10;
                other_nested_var_ts1755004212824 <= inj_data_in_1755004212823_781 - 20;
            end
        end
    end
    always_comb begin
        inj_out_nested_a_1755004212823_555 = split_nested_var_ts1755004212824;
        inj_out_nested_b_1755004212823_698 = other_nested_var_ts1755004212824;
    end
    // END: mod_split_nested_ts1755004212824
endmodule

