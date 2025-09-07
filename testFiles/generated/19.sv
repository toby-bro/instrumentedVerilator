module LintSensitiveList (
    input logic in_p,
    input logic in_q,
    output logic out_r
);
    always_comb begin
        out_r = in_p | in_q;
    end
endmodule

module shift_ops (
    input logic [7:0] data,
    input logic [2:0] shamt,
    output logic [7:0] left_shift,
    output logic [7:0] right_shift_arith,
    output logic [7:0] right_shift_logic
);
    assign left_shift = data << shamt;
    assign right_shift_logic = data >> shamt;
    assign right_shift_arith = data >>> shamt;
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755004209379_867,
    input logic inj_b_1755004209379_693,
    input logic [7:0] inj_data_1755004209379_911,
    input logic [15:0] inj_in1_1755004209380_128,
    input logic [15:0] inj_in2_1755004209380_364,
    input logic [15:0] inj_in3_1755004209380_610,
    input logic [15:0] inj_in4_1755004209380_601,
    input logic [15:0] inj_in5_1755004209380_550,
    input wire [7:0] inj_in_val1_1755004209380_71,
    input wire [7:0] inj_in_val2_1755004209380_152,
    input logic [2:0] inj_shamt_1755004209379_238,
    input wire reset,
    output logic [7:0] inj_left_shift_1755004209379_957,
    output logic inj_out_1755004209380_36,
    output logic inj_out_r_1755004209379_638,
    output logic [7:0] inj_out_ternary_result_1755004209380_101,
    output logic [7:0] inj_right_shift_arith_1755004209379_918,
    output logic [7:0] inj_right_shift_logic_1755004209379_280,
    output logic inj_sum_1755004209379_278
);
    // BEGIN: module_ternary_ts1755004209380
    // BEGIN: arith_comp_ops_ts1755004209380
    assign inj_out_1755004209380_36 = (inj_in1_1755004209380_128 + inj_in2_1755004209380_364) * inj_in3_1755004209380_610 > inj_in4_1755004209380_601 - inj_in5_1755004209380_550;
    // END: arith_comp_ops_ts1755004209380

    always_comb begin
    inj_out_ternary_result_1755004209380_101 = clk ? inj_in_val1_1755004209380_71 : inj_in_val2_1755004209380_152;
    end
    // END: module_ternary_ts1755004209380

    LintSensitiveList LintSensitiveList_inst_1755004209379_8422 (
        .in_p(inj_a_1755004209379_867),
        .in_q(inj_b_1755004209379_693),
        .out_r(inj_out_r_1755004209379_638)
    );
    simple_adder simple_adder_inst_1755004209379_5934 (
        .a(inj_a_1755004209379_867),
        .b(inj_b_1755004209379_693),
        .sum(inj_sum_1755004209379_278)
    );
    shift_ops shift_ops_inst_1755004209379_4076 (
        .right_shift_arith(inj_right_shift_arith_1755004209379_918),
        .right_shift_logic(inj_right_shift_logic_1755004209379_280),
        .data(inj_data_1755004209379_911),
        .shamt(inj_shamt_1755004209379_238),
        .left_shift(inj_left_shift_1755004209379_957)
    );
endmodule

