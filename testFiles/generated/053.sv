module split_conditional_reorder (
    input logic clk_cc,
    input logic condition_cc,
    input logic [7:0] val1_cc,
    input logic [7:0] val2_cc,
    input logic [7:0] val3_cc,
    output logic [7:0] out_reg_cc
);
    always @(posedge clk_cc) begin
        out_reg_cc <= val1_cc;
        if (condition_cc) begin
            out_reg_cc <= val2_cc;
        end else begin
            out_reg_cc <= val3_cc;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_a_1755007769262_621,
    input logic [7:0] inj_b_1755007769262_291,
    input logic [7:0] inj_c_1755007769262_0,
    input logic inj_condition_cc_1755007769262_690,
    input wire [15:0] inj_i_packed_data_1755007769263_97,
    input logic [2:0] inj_in_shift_1755007769262_749,
    input wire reset,
    output logic [7:0] inj_o_member_sum_1755007769263_968,
    output logic [3:0] inj_out_part_1755007769262_807,
    output logic [7:0] inj_out_reg_1755007769262_489,
    output logic [7:0] inj_out_reg_cc_1755007769262_591,
    output logic [7:0] inj_result_and_1755007769262_49,
    output logic [7:0] inj_result_or_1755007769262_972,
    output logic [7:0] inj_result_xor_1755007769262_72
);
    // BEGIN: BitwiseOperations_ts1755007769262
    // BEGIN: module_assignments_in_loops_ts1755007769263
    localparam int PART_START = 4;
    localparam int PART_WIDTH = 4;
    logic [7:0] reg_var_ts1755007769263;
    logic [3:0] part_var_ts1755007769263;
        // BEGIN: module_struct_ts1755007769264
        typedef struct packed {
            logic [3:0] part1_ts1755007769263;
            logic [7:0] part2_ts1755007769263;
            logic [3:0] part3_ts1755007769263;
        } my_packed_struct_t;
        my_packed_struct_t unpacked_data;
        assign unpacked_data = inj_i_packed_data_1755007769263_97;
        always @* begin
            inj_o_member_sum_1755007769263_968 = unpacked_data.part1_ts1755007769263 + unpacked_data.part2_ts1755007769263 + unpacked_data.part3_ts1755007769263;
        end
        // END: module_struct_ts1755007769264

    always_comb begin
        reg_var_ts1755007769263  = inj_a_1755007769262_621;
        part_var_ts1755007769263 = 4'h0;
        for (int i = 0; i < 4; i++) begin
            reg_var_ts1755007769263  = reg_var_ts1755007769263 + i;
            reg_var_ts1755007769263 += (i * 2);
            reg_var_ts1755007769263 <<= inj_in_shift_1755007769262_749;
            reg_var_ts1755007769263[i % 8] = (reg_var_ts1755007769263[i % 8] == 1'b0);
            reg_var_ts1755007769263[PART_START +: PART_WIDTH] = i[3:0];
        end
        part_var_ts1755007769263 = reg_var_ts1755007769263[7:4];
    end
    assign inj_out_reg_1755007769262_489  = reg_var_ts1755007769263;
    assign inj_out_part_1755007769262_807 = part_var_ts1755007769263;
    // END: module_assignments_in_loops_ts1755007769263

    split_conditional_reorder split_conditional_reorder_inst_1755007769262_7579 (
        .condition_cc(inj_condition_cc_1755007769262_690),
        .val1_cc(inj_b_1755007769262_291),
        .val2_cc(inj_a_1755007769262_621),
        .val3_cc(inj_c_1755007769262_0),
        .out_reg_cc(inj_out_reg_cc_1755007769262_591),
        .clk_cc(clk)
    );
    assign inj_result_and_1755007769262_49 = inj_a_1755007769262_621 & inj_b_1755007769262_291;
    assign inj_result_or_1755007769262_972 = inj_a_1755007769262_621 | inj_c_1755007769262_0;
    assign inj_result_xor_1755007769262_72 = inj_b_1755007769262_291 ^ inj_c_1755007769262_0;
    // END: BitwiseOperations_ts1755007769262
endmodule

