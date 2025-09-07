module dup_compare (
    input int val_a,
    input int val_b,
    input int val_c,
    output logic [5:0] indicators
);
    always_comb begin
        indicators = '0;
        indicators[0] = (val_a == val_b);
        indicators[1] = (val_a != val_b);
        indicators[2] = (val_a > val_b);
        indicators[3] = (val_a < val_b);
        indicators[4] = (val_a >= val_b);
        indicators[5] = (val_a <= val_b);
        if (val_b == val_c) begin
            indicators = indicators | 6'b111111;
        end
        if (val_a > val_c) begin
            indicators = indicators & 6'b000000;
        end
        if ((val_a < val_b) && (val_b > val_c)) begin
            indicators[0] = 1;
        end else if ((val_a >= val_b) || (val_b <= val_c)) begin
            indicators[1] = 1;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_in_1755007792680_581,
    input bit [3:0] inj_in_data_1755007792681_116,
    input logic [15:0] inj_packed_in_1755007792681_352,
    input logic inj_unused_in_1755007792680_654,
    input int inj_val_a_1755007792680_720,
    input int inj_val_b_1755007792680_20,
    input int inj_val_c_1755007792680_230,
    input wire reset,
    output logic [7:0] inj_byte_out_1755007792681_250,
    output logic [5:0] inj_indicators_1755007792680_673,
    output wire inj_o_c_1755007792680_203,
    output logic [7:0] inj_out_1755007792680_865,
    output bit [3:0] inj_out_result_1755007792681_571,
    output logic [15:0] inj_packed_out_1755007792681_179,
    output logic inj_unused_out_1755007792680_200
);
    // BEGIN: simple_assign_ts1755007792680
    // BEGIN: unreferenced_module_ts1755007792680
    // BEGIN: module_simple_ts1755007792680
    wire internal_xor_res_ts1755007792680;
        // BEGIN: PackedStructOps_ts1755007792682
        typedef struct packed {
            logic [7:0] low_ts1755007792681;
            logic [7:0] high_ts1755007792681;
        } pair_t;
        pair_t data_pair;
        assign data_pair.high_ts1755007792681 = inj_packed_in_1755007792681_352[15:8];
        assign data_pair.low_ts1755007792681 = inj_in_1755007792680_581;
        assign inj_byte_out_1755007792681_250 = data_pair.high_ts1755007792681;
        assign inj_packed_out_1755007792681_179[15:8] = data_pair.high_ts1755007792681;
        assign inj_packed_out_1755007792681_179[7:0] = data_pair.low_ts1755007792681 + inj_in_1755007792680_581;
        // END: PackedStructOps_ts1755007792682

        // BEGIN: mod_if_else_simple_ts1755007792681
    always_comb begin
        if (inj_in_data_1755007792681_116 > 8) begin
            inj_out_result_1755007792681_571 = inj_in_data_1755007792681_116 + 1;
        end else begin
            inj_out_result_1755007792681_571 = inj_in_data_1755007792681_116 - 1;
        end
    end
        // END: mod_if_else_simple_ts1755007792681

    assign internal_xor_res_ts1755007792680 = clk ^ reset;
    assign inj_o_c_1755007792680_203 = internal_xor_res_ts1755007792680 & clk;
    // END: module_simple_ts1755007792680

    assign inj_unused_out_1755007792680_200 = ~inj_unused_in_1755007792680_654;
    // END: unreferenced_module_ts1755007792680

    dup_compare dup_compare_inst_1755007792680_1825 (
        .val_a(inj_val_a_1755007792680_720),
        .val_b(inj_val_b_1755007792680_20),
        .val_c(inj_val_c_1755007792680_230),
        .indicators(inj_indicators_1755007792680_673)
    );
    assign inj_out_1755007792680_865 = inj_in_1755007792680_581;
    // END: simple_assign_ts1755007792680
endmodule

