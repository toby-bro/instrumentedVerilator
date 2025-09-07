module child_empty_ports (
    p1,
    p2
);
    input logic p1;
    output logic p2;
    assign p2 = p1;
endmodule

module loop_with_internal_assign (
    input logic [3:0] start_val,
    output logic [7:0] final_val
);
    logic [7:0] current_val;
    always_comb begin
        current_val = start_val;
        for (int k = 0; k < 3; k = k + 1) begin
            current_val = current_val + 1;
        end
        final_val = current_val;
    end
endmodule

module split_conditional_blocking (
    input logic condition_o,
    input logic [7:0] in_false_o,
    input logic [7:0] in_true_o,
    output logic [7:0] out_val_o
);
    always @(*) begin
        if (condition_o) begin
            out_val_o = in_true_o;
        end else begin
            out_val_o = in_false_o;
        end
    end
endmodule

module split_input_only_var (
    input logic clk_k,
    input logic control_signal_k,
    input logic [7:0] data_in_k,
    output logic [7:0] data_out_k
);
    always @(posedge clk_k) begin
        if (control_signal_k) begin
            data_out_k <= data_in_k;
        end
    end
endmodule

module variable_sel_mux (
    input logic [7:0] in,
    input logic [2:0] index,
    output logic out
);
    assign out = in[index];
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_in_1755007854832_704,
    input logic inj_in_h_1755007854832_153,
    input logic [2:0] inj_index_1755007854832_72,
    input logic [3:0] inj_start_val_1755007854832_234,
    input wire reset,
    output logic [3:0] inj_data_out_1755007854837_636,
    output logic [7:0] inj_data_out_k_1755007854836_48,
    output logic inj_dout_1755007854833_318,
    output logic [7:0] inj_final_val_1755007854832_707,
    output logic inj_out_1755007854832_860,
    output logic [1:0] inj_out_bits_1755007854835_527,
    output logic inj_out_i_1755007854832_945,
    output logic [7:0] inj_out_val_o_1755007854836_405,
    output logic inj_p2_1755007854838_566,
    output logic inj_reset_n_1755007854835_442
);
    // BEGIN: LintAsyncFovIssue_ts1755007854832
    // BEGIN: ModRegister_ts1755007854834
    // BEGIN: cast_select_demo_ts1755007854835
    logic [7:0] internal_ts1755007854835;
        child_empty_ports child_empty_ports_inst_1755007854838_1108 (
            .p1(inj_in_h_1755007854832_153),
            .p2(inj_p2_1755007854838_566)
        );
        // BEGIN: GenerateFor_ts1755007854837
        genvar i;
        generate
            for (i = 0; i < 4; i = i + 1) begin : g_loop
                assign inj_data_out_1755007854837_636[i] = inj_start_val_1755007854832_234[i];
            end
        endgenerate
        // END: GenerateFor_ts1755007854837

        split_input_only_var split_input_only_var_inst_1755007854836_4101 (
            .clk_k(clk),
            .control_signal_k(inj_in_h_1755007854832_153),
            .data_in_k(internal_ts1755007854835),
            .data_out_k(inj_data_out_k_1755007854836_48)
        );
        split_conditional_blocking split_conditional_blocking_inst_1755007854836_8317 (
            .condition_o(inj_in_h_1755007854832_153),
            .in_false_o(internal_ts1755007854835),
            .in_true_o(inj_in_1755007854832_704),
            .out_val_o(inj_out_val_o_1755007854836_405)
        );
        // BEGIN: ansi_basic_ts1755007854835
        always_comb begin
            inj_reset_n_1755007854835_442 = clk;
        end
        // END: ansi_basic_ts1755007854835

    always_comb begin
        internal_ts1755007854835 = inj_in_1755007854832_704;
        inj_out_bits_1755007854835_527 = internal_ts1755007854835[3 -: 2];
    end
    // END: cast_select_demo_ts1755007854835

    always @* begin
        inj_dout_1755007854833_318 = inj_in_h_1755007854832_153;
    end
    // END: ModRegister_ts1755007854834

    loop_with_internal_assign loop_with_internal_assign_inst_1755007854832_6023 (
        .start_val(inj_start_val_1755007854832_234),
        .final_val(inj_final_val_1755007854832_707)
    );
    always_ff @(posedge clk or negedge reset) begin
        if (!reset) begin
            inj_out_i_1755007854832_945 <= 1'b0;
        end else begin
            inj_out_i_1755007854832_945 <= inj_in_h_1755007854832_153 & inj_out_i_1755007854832_945;
        end
    end
    // END: LintAsyncFovIssue_ts1755007854832

    variable_sel_mux variable_sel_mux_inst_1755007854832_829 (
        .index(inj_index_1755007854832_72),
        .out(inj_out_1755007854832_860),
        .in(inj_in_1755007854832_704)
    );
endmodule

