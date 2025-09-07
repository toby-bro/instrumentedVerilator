module snippet (
    input wire clk,
    input wire [15:0] inj_in_packed_data_1755007872969_853,
    input wire reset,
    output wire [7:0] inj_out_byte_1755007872969_689
);
    // BEGIN: packed_struct_module_ts1755007872969
    typedef struct packed {
        logic [7:0] byte1_ts1755007872969;
        logic [7:0] byte2_ts1755007872969;
    } my_packed_struct_t;
    my_packed_struct_t data_struct;
    assign data_struct = inj_in_packed_data_1755007872969_853;
    assign inj_out_byte_1755007872969_689 = data_struct.byte1_ts1755007872969;
    // END: packed_struct_module_ts1755007872969
endmodule

