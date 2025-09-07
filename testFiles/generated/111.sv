module PackedStructOps (
    input logic [7:0] byte_val,
    input logic [15:0] packed_in,
    output logic [7:0] byte_out,
    output logic [15:0] packed_out
);
    typedef struct packed {
        logic [7:0] low;
        logic [7:0] high;
    } pair_t;
    pair_t data_pair;
    assign data_pair.high = packed_in[15:8];
    assign data_pair.low = byte_val;
    assign byte_out = data_pair.high;
    assign packed_out[15:8] = data_pair.high;
    assign packed_out[7:0] = data_pair.low + byte_val;
endmodule

module nested_macro_expansion (
    input int in_val,
    output int out_val
);
    `define LVL1(x) ((x) + 1)
    `define LVL2(y) `LVL1((y) * 2)
    `define LVL3(z) `LVL2((z) / 3)
    int nested_result;
    always_comb begin
        nested_result = `LVL3(`LVL1(in_val));
    end
    assign out_val = nested_result;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_byte_val_1755007789801_243,
    input logic [15:0] inj_in1_1755007789801_894,
    input logic [15:0] inj_in2_1755007789801_172,
    input logic [15:0] inj_in4_1755007789801_947,
    input logic [15:0] inj_in5_1755007789801_584,
    input int inj_in_val_1755007789801_194,
    input logic [15:0] inj_packed_in_1755007789801_965,
    input wire reset,
    output logic [7:0] inj_byte_out_1755007789801_333,
    output wire inj_match_x_neq_1755007789801_616,
    output wire inj_match_z_eq_1755007789801_579,
    output logic inj_out_1755007789801_853,
    output int inj_out_val_1755007789801_152,
    output logic [15:0] inj_packed_out_1755007789801_893,
    inout wire [3:0] inj_data_io_1755007789801_258
);
    // BEGIN: CaseEq_ts1755007789801
    // BEGIN: arith_comp_ops_ts1755007789801
    assign inj_out_1755007789801_853 = (inj_in1_1755007789801_894 + inj_in2_1755007789801_172) * inj_packed_in_1755007789801_965 > inj_in4_1755007789801_947 - inj_in5_1755007789801_584;
    // END: arith_comp_ops_ts1755007789801

    PackedStructOps PackedStructOps_inst_1755007789801_7740 (
        .byte_val(inj_byte_val_1755007789801_243),
        .packed_in(inj_packed_in_1755007789801_965),
        .byte_out(inj_byte_out_1755007789801_333),
        .packed_out(inj_packed_out_1755007789801_893)
    );
    nested_macro_expansion nested_macro_expansion_inst_1755007789801_7947 (
        .in_val(inj_in_val_1755007789801_194),
        .out_val(inj_out_val_1755007789801_152)
    );
    assign inj_match_z_eq_1755007789801_579 = (inj_data_io_1755007789801_258 === 4'b101z);
    assign inj_match_x_neq_1755007789801_616 = (inj_data_io_1755007789801_258 !== 4'b1x0x);
    // END: CaseEq_ts1755007789801
endmodule

