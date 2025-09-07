module Bit_Manip (
    input wire [1:0] byte_idx,
    input wire [31:0] wide_data,
    output reg [7:0] selected_byte
);
    always_comb begin
        case (byte_idx)
            2'b00: selected_byte = wide_data[7:0];
            2'b01: selected_byte = wide_data[15:8];
            2'b10: selected_byte = wide_data[23:16];
            default: selected_byte = wide_data[31:24];
        endcase
    end
endmodule

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
    input wire [1:0] inj_byte_idx_1755007832767_406,
    input logic [7:0] inj_data_1755007832767_77,
    input logic [2:0] inj_shift_val_1755007832767_672,
    input wire [31:0] inj_wide_data_1755007832767_487,
    input wire reset,
    output logic [7:0] inj_left_shift_log_1755007832767_459,
    output logic [7:0] inj_right_shift_arith_1755007832767_385,
    output logic [7:0] inj_right_shift_log_1755007832767_878,
    output reg [7:0] inj_selected_byte_1755007832767_396
);
    ShiftOperations ShiftOperations_inst_1755007832767_4767 (
        .data(inj_data_1755007832767_77),
        .shift_val(inj_shift_val_1755007832767_672),
        .left_shift_log(inj_left_shift_log_1755007832767_459),
        .right_shift_arith(inj_right_shift_arith_1755007832767_385),
        .right_shift_log(inj_right_shift_log_1755007832767_878)
    );
    Bit_Manip Bit_Manip_inst_1755007832767_5772 (
        .byte_idx(inj_byte_idx_1755007832767_406),
        .wide_data(inj_wide_data_1755007832767_487),
        .selected_byte(inj_selected_byte_1755007832767_396)
    );
endmodule

