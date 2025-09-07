module snippet (
    input wire clk,
    input integer inj_in_int_1755007822199_413,
    input logic [31:0] inj_in_l32_1755007822199_12,
    input logic signed [7:0] inj_in_s8_1755007822199_317,
    input logic [15:0] inj_in_u16_1755007822199_366,
    input wire reset,
    output logic signed [15:0] inj_out_s16_1755007822199_401,
    output logic signed [31:0] inj_out_s32_from_int_1755007822199_453,
    output logic signed [31:0] inj_out_s32_from_l32_1755007822199_688,
    output logic [31:0] inj_out_u32_from_int_1755007822199_182,
    output logic [31:0] inj_out_u32_from_l32_1755007822199_469,
    output logic [7:0] inj_out_u8_1755007822199_361
);
    // BEGIN: SignedUnsignedConversions_ts1755007822199
    always_comb begin
        inj_out_u8_1755007822199_361 = $unsigned(inj_in_s8_1755007822199_317);
        inj_out_s16_1755007822199_401 = $signed(inj_in_u16_1755007822199_366);
        inj_out_s32_from_l32_1755007822199_688 = $signed(inj_in_l32_1755007822199_12);
        inj_out_u32_from_l32_1755007822199_469 = $unsigned(inj_in_l32_1755007822199_12);
        inj_out_s32_from_int_1755007822199_453 = $signed(inj_in_int_1755007822199_413);
        inj_out_u32_from_int_1755007822199_182 = $unsigned(inj_in_int_1755007822199_413);
    end
    // END: SignedUnsignedConversions_ts1755007822199
endmodule

