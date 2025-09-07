module snippet (
    input wire clk,
    input wire [15:0] inj_i_packed_data_1755007846868_670,
    input wire reset,
    output logic [7:0] inj_o_member_sum_1755007846868_749
);
    // BEGIN: module_struct_ts1755007846868
    typedef struct packed {
        logic [3:0] part1_ts1755007846868;
        logic [7:0] part2_ts1755007846868;
        logic [3:0] part3_ts1755007846868;
    } my_packed_struct_t;
    my_packed_struct_t unpacked_data;
    assign unpacked_data = inj_i_packed_data_1755007846868_670;
    always @* begin
        inj_o_member_sum_1755007846868_749 = unpacked_data.part1_ts1755007846868 + unpacked_data.part2_ts1755007846868 + unpacked_data.part3_ts1755007846868;
    end
    // END: module_struct_ts1755007846868
endmodule

