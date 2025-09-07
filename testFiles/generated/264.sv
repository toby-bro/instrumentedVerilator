module Comb_IfElse (
    input wire condition,
    input wire [15:0] value1,
    input wire [15:0] value2,
    output reg [15:0] result_val
);
    always_comb begin
        if (condition) begin
            result_val = value1;
        end else begin
            result_val = value2;
        end
    end
endmodule

module casez_xz_alt (
    input logic [2:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            3'b1?z: out_res = 1'b1;
            3'b0z?: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module snippet #(
    parameter bit GEN = 1
) (
    input wire clk,
    input logic inj_in1_1755007842714_339,
    input logic inj_in2_1755007842714_445,
    input logic [2:0] inj_in_val_1755007842717_968,
    input logic [31:0] inj_in_vec_1755007842712_857,
    input int inj_start_index_1755007842712_357,
    input wire [15:0] inj_value1_1755007842713_130,
    input wire [15:0] inj_value2_1755007842713_913,
    input wire [63:0] inj_wide_a_1755007842715_96,
    input wire [63:0] inj_wide_b_1755007842715_373,
    input int inj_width_1755007842712_366,
    input wire reset,
    output wire [127:0] inj_concat_out_1755007842715_50,
    output logic inj_out_1755007842714_201,
    output logic [7:0] inj_out_down_1755007842712_457,
    output reg inj_out_res_1755007842717_963,
    output logic [7:0] inj_out_up_1755007842712_416,
    output wire [7:0] inj_reduce_xor_out_1755007842715_480,
    output reg [15:0] inj_result_val_1755007842713_160,
    output logic inj_sig_out_1755007842716_781,
    output wire [63:0] inj_wide_sum_1755007842715_862
);
    // BEGIN: range_select_indexed_packed_ts1755007842713
    // BEGIN: simple_xor_gate_ts1755007842714
    // BEGIN: wide_bus_ops_ts1755007842715
    // BEGIN: GenerateIfParam_ts1755007842716
    casez_xz_alt casez_xz_alt_inst_1755007842717_5337 (
        .in_val(inj_in_val_1755007842717_968),
        .out_res(inj_out_res_1755007842717_963)
    );
    generate
        if (GEN) begin : g_true
            assign inj_sig_out_1755007842716_781 = inj_in1_1755007842714_339;
        end
        else begin : g_false
            assign inj_sig_out_1755007842716_781 = ~inj_in1_1755007842714_339;
        end
    endgenerate
    // END: GenerateIfParam_ts1755007842716

    assign inj_wide_sum_1755007842715_862 = inj_wide_a_1755007842715_96 + inj_wide_b_1755007842715_373;
    assign inj_reduce_xor_out_1755007842715_480 = ^inj_wide_a_1755007842715_96[63:0];
    assign inj_concat_out_1755007842715_50 = {inj_wide_a_1755007842715_96, inj_wide_b_1755007842715_373};
    // END: wide_bus_ops_ts1755007842715

    assign inj_out_1755007842714_201 = inj_in1_1755007842714_339 ^ inj_in2_1755007842714_445;
    // END: simple_xor_gate_ts1755007842714

    Comb_IfElse Comb_IfElse_inst_1755007842713_5572 (
        .value1(inj_value1_1755007842713_130),
        .value2(inj_value2_1755007842713_913),
        .result_val(inj_result_val_1755007842713_160),
        .condition(clk)
    );
    always_comb begin
        if (inj_start_index_1755007842712_357 >= 0 && inj_width_1755007842712_366 > 0 && inj_start_index_1755007842712_357 + inj_width_1755007842712_366 <= 32) begin
            case (inj_width_1755007842712_366)
                1: inj_out_up_1755007842712_416 = inj_in_vec_1755007842712_857[inj_start_index_1755007842712_357 +: 1];
                2: inj_out_up_1755007842712_416 = inj_in_vec_1755007842712_857[inj_start_index_1755007842712_357 +: 2];
                4: inj_out_up_1755007842712_416 = inj_in_vec_1755007842712_857[inj_start_index_1755007842712_357 +: 4];
                8: inj_out_up_1755007842712_416 = inj_in_vec_1755007842712_857[inj_start_index_1755007842712_357 +: 8];
                default: inj_out_up_1755007842712_416 = 'x;
            endcase
        end else begin
            inj_out_up_1755007842712_416 = 'x;
        end
        if (inj_start_index_1755007842712_357 >= inj_width_1755007842712_366 - 1 && inj_width_1755007842712_366 > 0 && inj_start_index_1755007842712_357 < 32) begin
            case (inj_width_1755007842712_366)
                1: inj_out_down_1755007842712_457 = inj_in_vec_1755007842712_857[inj_start_index_1755007842712_357 -: 1];
                2: inj_out_down_1755007842712_457 = inj_in_vec_1755007842712_857[inj_start_index_1755007842712_357 -: 2];
                4: inj_out_down_1755007842712_457 = inj_in_vec_1755007842712_857[inj_start_index_1755007842712_357 -: 4];
                8: inj_out_down_1755007842712_457 = inj_in_vec_1755007842712_857[inj_start_index_1755007842712_357 -: 8];
                default: inj_out_down_1755007842712_457 = 'x;
            endcase
        end else begin
            inj_out_down_1755007842712_457 = 'x;
        end
    end
    // END: range_select_indexed_packed_ts1755007842713
endmodule

