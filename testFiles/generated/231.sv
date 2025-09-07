module snippet (
    input wire clk,
    input logic [3:0] inj_i_addr_arr_1755007831451_456,
    input logic [3:0] inj_i_addr_sel_1755007831451_584,
    input logic [7:0] inj_i_vector_1755007831451_359,
    input wire reset,
    output logic [7:0] inj_o_array_var_elem_1755007831451_734,
    output logic inj_o_sel_var_bit_1755007831451_430
);
    // BEGIN: HandleOutOfBoundsRead_ts1755007831452
    parameter ARR_SIZE = 4;
    logic [7:0] my_array_ts1755007831451 [0:ARR_SIZE-1];
    assign my_array_ts1755007831451[0] = 8'd10;
    assign my_array_ts1755007831451[1] = 8'd20;
    assign my_array_ts1755007831451[2] = 8'd30;
    assign my_array_ts1755007831451[3] = 8'd40;
    assign inj_o_sel_var_bit_1755007831451_430 = inj_i_vector_1755007831451_359[inj_i_addr_sel_1755007831451_584];
    assign inj_o_array_var_elem_1755007831451_734 = my_array_ts1755007831451[inj_i_addr_arr_1755007831451_456];
    // END: HandleOutOfBoundsRead_ts1755007831452
endmodule

