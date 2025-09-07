module ProgramDefinition (
    input wire clk,
    input wire in_pd,
    input logic [7:0] inj_byte_val_1755538476222_980,
    input logic inj_cond_in_1755538476223_6,
    input logic [15:0] inj_packed_in_1755538476222_929,
    input wire rst,
    output logic [7:0] inj_byte_out_1755538476222_532,
    output logic inj_cond_out_1755538476223_834,
    output logic [15:0] inj_packed_out_1755538476222_376,
    output logic out_pd
);
    // BEGIN: PackedStructOps_ts1755538476222
    typedef struct packed {
        logic [7:0] low_ts1755538476222;
        logic [7:0] high_ts1755538476222;
    } pair_t;
    pair_t data_pair;
    // BEGIN: mod_logical_not_ts1755538476223
    always_comb begin
        inj_cond_out_1755538476223_834 = !inj_cond_in_1755538476223_6;
    end
    // END: mod_logical_not_ts1755538476223

    assign data_pair.high_ts1755538476222 = inj_packed_in_1755538476222_929[15:8];
    assign data_pair.low_ts1755538476222 = inj_byte_val_1755538476222_980;
    assign inj_byte_out_1755538476222_532 = data_pair.high_ts1755538476222;
    assign inj_packed_out_1755538476222_376[15:8] = data_pair.high_ts1755538476222;
    assign inj_packed_out_1755538476222_376[7:0] = data_pair.low_ts1755538476222 + inj_byte_val_1755538476222_980;
    // END: PackedStructOps_ts1755538476222

    assign out_pd = in_pd;
endmodule

