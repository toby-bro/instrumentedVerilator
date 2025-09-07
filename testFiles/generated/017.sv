module mod_case_unique_priority (
    input bit [2:0] in_state_case,
    output bit out_priority_case,
    output bit out_unique_case
);
always_comb begin
    out_unique_case = 1'b0;
    unique case (in_state_case)
        3'd0: out_unique_case = 1'b0;
        3'd1: out_unique_case = 1'b1;
        3'd2: out_unique_case = 1'b0;
        3'd1: out_unique_case = 1'b1;
        default: out_unique_case = 1'b1;
    endcase
end
always_comb begin
    out_priority_case = 1'b0;
    priority case (in_state_case)
        3'd0: out_priority_case = 1'b0;
        3'd1: out_priority_case = 1'b1;
        3'd2: out_priority_case = 1'b0;
        3'd1: out_priority_case = 1'b1;
        default: out_priority_case = 1'b1;
    endcase
end
endmodule

module non_ansi_basic (
    non_ansi_a,
    non_ansi_basic_input,
    non_ansi_b,
    non_ansi_basic_output
);
    input wire non_ansi_a;
    output reg non_ansi_b;
    input logic non_ansi_basic_input;
    output logic non_ansi_basic_output;
    always_comb begin
        non_ansi_b = non_ansi_a;
        non_ansi_basic_output = non_ansi_basic_input;
    end
endmodule

module snippet (
    input wire clk,
    input bit inj_cfg_in_1755007755956_902,
    input logic [31:0] inj_data_in_1755007755954_889,
    input logic [7:0] inj_in1_1755007755954_644,
    input logic [7:0] inj_in2_1755007755954_864,
    input bit [2:0] inj_in_state_case_1755007755957_974,
    input int inj_index_in_1755007755954_437,
    input logic inj_non_ansi_basic_input_1755007755954_71,
    input logic [4:0] inj_start_bit_1755007755954_1,
    input wire reset,
    output logic inj_bit_out_1755007755954_84,
    output logic [7:0] inj_byte_out_1755007755954_416,
    output bit inj_cfg_out_1755007755956_366,
    output reg inj_non_ansi_b_1755007755954_389,
    output logic inj_non_ansi_basic_output_1755007755954_341,
    output logic [7:0] inj_out1_1755007755954_282,
    output logic [7:0] inj_out2_1755007755954_887,
    output bit inj_out_priority_case_1755007755957_376,
    output bit inj_out_unique_case_1755007755957_698
);
    // BEGIN: ArrayIndexAndPartSelect_ts1755007755954
    logic [31:0] internal_data = inj_data_in_1755007755954_889;
    // BEGIN: dup_expr_ts1755007755955
    logic [7:0] temp_add_ts1755007755955;
    logic [7:0] temp_mult_ts1755007755955;
    logic [7:0] inter1_ts1755007755955;
    logic [7:0] inter2_ts1755007755955;
    logic [7:0] complex_expr_ts1755007755955;
        mod_case_unique_priority mod_case_unique_priority_inst_1755007755957_9324 (
            .in_state_case(inj_in_state_case_1755007755957_974),
            .out_priority_case(inj_out_priority_case_1755007755957_376),
            .out_unique_case(inj_out_unique_case_1755007755957_698)
        );
        // BEGIN: Module_ConfigKeywords_ts1755007755956
        assign inj_cfg_out_1755007755956_366 = inj_cfg_in_1755007755956_902;
        // END: Module_ConfigKeywords_ts1755007755956

    always_comb begin
        temp_add_ts1755007755955 = inj_in1_1755007755954_644 + inj_in2_1755007755954_864;
        inj_out1_1755007755954_282 = temp_add_ts1755007755955;
        inj_out2_1755007755954_887 = inj_in1_1755007755954_644 + inj_in2_1755007755954_864;
        inter1_ts1755007755955 = inj_in1_1755007755954_644 * 2;
        inter2_ts1755007755955 = inj_in2_1755007755954_864 * 2;
        temp_mult_ts1755007755955 = inter1_ts1755007755955 + inter2_ts1755007755955;
        complex_expr_ts1755007755955 = (inj_in1_1755007755954_644 + inj_in2_1755007755954_864) * (inj_in1_1755007755954_644 - inj_in2_1755007755954_864) + (inj_in1_1755007755954_644 + inj_in2_1755007755954_864);
        if (inj_in1_1755007755954_644 > inj_in2_1755007755954_864) begin
            inj_out1_1755007755954_282 = temp_mult_ts1755007755955;
        end else begin
            inj_out1_1755007755954_282 = temp_add_ts1755007755955;
        end
        if (inj_in2_1755007755954_864 >= inj_in1_1755007755954_644) begin
            inj_out2_1755007755954_887 = temp_add_ts1755007755955;
        end else begin
            inj_out2_1755007755954_887 = temp_mult_ts1755007755955;
        end
        inj_out1_1755007755954_282 = inj_out1_1755007755954_282 + complex_expr_ts1755007755955;
    end
    // END: dup_expr_ts1755007755955

    non_ansi_basic non_ansi_basic_inst_1755007755954_4129 (
        .non_ansi_basic_input(inj_non_ansi_basic_input_1755007755954_71),
        .non_ansi_basic_output(inj_non_ansi_basic_output_1755007755954_341),
        .non_ansi_a(clk),
        .non_ansi_b(inj_non_ansi_b_1755007755954_389)
    );
    assign inj_bit_out_1755007755954_84 = internal_data[inj_index_in_1755007755954_437];
    assign inj_byte_out_1755007755954_416 = internal_data[inj_start_bit_1755007755954_1 +: 8];
    // END: ArrayIndexAndPartSelect_ts1755007755954
endmodule

