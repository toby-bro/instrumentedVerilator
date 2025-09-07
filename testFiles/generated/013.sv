module snippet #(
    parameter integer DATA_WIDTH = 8
) (
    input wire clk,
    input logic [15:0] inj_in_vector_1755007754619_560,
    input wire [7:0] inj_param_in_1755007754619_589,
    input wire reset,
    output logic [7:0] inj_out_slice_1755007754619_973,
    output wire [7:0] inj_param_out_1755007754619_375
);
    // BEGIN: module_with_params_ts1755007754619
    // BEGIN: MiscExpressions_ValueRange_ts1755007754619
    always_comb begin
        inj_out_slice_1755007754619_973 = inj_in_vector_1755007754619_560[7:0];
    end
    // END: MiscExpressions_ValueRange_ts1755007754619

    assign inj_param_out_1755007754619_375 = inj_param_in_1755007754619_589;
    // END: module_with_params_ts1755007754619
endmodule

