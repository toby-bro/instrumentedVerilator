module ShiftOperations (
    input logic [7:0] data,
    input logic [2:0] shift_val,
    output logic [7:0] left_shift_log,
    output logic [7:0] right_shift_arith,
    output logic [7:0] right_shift_log
);
    assign left_shift_log = data << shift_val;
    assign right_shift_log = data >> shift_val;
    assign right_shift_arith = $signed(data) >>> shift_val;
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_a_1755007874525_743,
    input logic [3:0] inj_b_1755007874525_601,
    input logic [7:0] inj_c_1755007874525_266,
    input logic [15:0] inj_in_1755007874524_624,
    input logic inj_in_a_1755007874524_612,
    input logic [2:0] inj_shift_val_1755007874525_829,
    input wire reset,
    output logic [7:0] inj_left_shift_log_1755007874525_712,
    output logic [15:0] inj_out_1755007874524_274,
    output logic inj_out_a_1755007874524_952,
    output logic [15:0] inj_out_concat_1755007874525_182,
    output logic [7:0] inj_right_shift_arith_1755007874525_635,
    output logic [7:0] inj_right_shift_log_1755007874525_931
);
    // BEGIN: always_comb_assign_ts1755007874524
    // BEGIN: mod_name_conflict_ts1755007874525
    logic conflict_var_ts1755007874524;
        ShiftOperations ShiftOperations_inst_1755007874525_1505 (
            .left_shift_log(inj_left_shift_log_1755007874525_712),
            .right_shift_arith(inj_right_shift_arith_1755007874525_635),
            .right_shift_log(inj_right_shift_log_1755007874525_931),
            .data(inj_c_1755007874525_266),
            .shift_val(inj_shift_val_1755007874525_829)
        );
        // BEGIN: ConcatVectorOps_ts1755007874525
        assign inj_out_concat_1755007874525_182 = {inj_a_1755007874525_743, inj_b_1755007874525_601, inj_c_1755007874525_266};
        // END: ConcatVectorOps_ts1755007874525

    parameter int conflict_param = 1;
    assign inj_out_a_1755007874524_952 = inj_in_a_1755007874524_612;
    // END: mod_name_conflict_ts1755007874525

    always_comb begin
        inj_out_1755007874524_274 = inj_in_1755007874524_624;
    end
    // END: always_comb_assign_ts1755007874524
endmodule

