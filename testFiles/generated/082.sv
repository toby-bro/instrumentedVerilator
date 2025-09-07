module snippet (
    input wire clk,
    input logic [15:0] inj_in_vec_1755007779438_170,
    input wire reset,
    output logic [7:0] inj_out_slice_be_1755007779438_518,
    output logic [7:0] inj_out_slice_le_1755007779438_792
);
    // BEGIN: range_select_simple_packed_ts1755007779438
    assign inj_out_slice_be_1755007779438_518 = inj_in_vec_1755007779438_170[7:0]; 
    assign inj_out_slice_le_1755007779438_792 = inj_in_vec_1755007779438_170[7:0]; 
    // END: range_select_simple_packed_ts1755007779438
endmodule

