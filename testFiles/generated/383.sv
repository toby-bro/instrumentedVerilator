module split_ifelse_chain (
    input logic c1_x,
    input logic c2_x,
    input logic c3_x,
    input logic clk_x,
    input logic [7:0] v1_x,
    input logic [7:0] v2_x,
    input logic [7:0] v3_x,
    input logic [7:0] v4_x,
    output logic [7:0] out_x
);
    always @(posedge clk_x) begin
        if (c1_x) begin
            out_x <= v1_x;
        end else if (c2_x) begin
            out_x <= v2_x;
        end else if (c3_x) begin
            out_x <= v3_x;
        end else begin
            out_x <= v4_x;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_c1_x_1755007882722_174,
    input logic inj_c2_x_1755007882723_860,
    input logic inj_c3_x_1755007882722_536,
    input logic [15:0] inj_in_vector_1755007882722_352,
    input logic [7:0] inj_v1_x_1755007882722_951,
    input logic [7:0] inj_v2_x_1755007882723_852,
    input logic [7:0] inj_v3_x_1755007882722_174,
    input logic [7:0] inj_v4_x_1755007882723_102,
    input wire reset,
    output logic [7:0] inj_out_slice_1755007882722_280,
    output logic [7:0] inj_out_x_1755007882722_923
);
    // BEGIN: MiscExpressions_ValueRange_ts1755007882722
    split_ifelse_chain split_ifelse_chain_inst_1755007882723_8821 (
        .c1_x(inj_c1_x_1755007882722_174),
        .v1_x(inj_v1_x_1755007882722_951),
        .c2_x(inj_c2_x_1755007882723_860),
        .clk_x(clk),
        .out_x(inj_out_x_1755007882722_923),
        .v3_x(inj_v3_x_1755007882722_174),
        .c3_x(inj_c3_x_1755007882722_536),
        .v2_x(inj_v2_x_1755007882723_852),
        .v4_x(inj_v4_x_1755007882723_102)
    );
    always_comb begin
        inj_out_slice_1755007882722_280 = inj_in_vector_1755007882722_352[7:0];
    end
    // END: MiscExpressions_ValueRange_ts1755007882722
endmodule

