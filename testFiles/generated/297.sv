module snippet (
    input wire clk,
    input logic inj_a_1755007854495_263,
    input logic inj_b_1755007854495_188,
    input logic [31:0] inj_input_pa_1755007854496_519,
    input logic [3:0] inj_input_slice_pa_1755007854495_176,
    input wire reset,
    output logic [7:0] inj_output_pa_1755007854495_252,
    output logic [7:0] inj_output_pa_element1_1755007854496_349,
    output logic inj_sum_1755007854495_933
);
    // BEGIN: simple_adder_ts1755007854495
    // BEGIN: module_packed_array_ts1755007854496
    logic [7:0] my_packed_array[0:3] ;
    always_comb begin
        if (inj_a_1755007854495_263) begin
            my_packed_array[0] = inj_input_pa_1755007854496_519[7:0];
            my_packed_array[1] = inj_input_pa_1755007854496_519[15:8];
            my_packed_array[2] = inj_input_pa_1755007854496_519[23:16];
            my_packed_array[3] = my_packed_array[0] + my_packed_array[1];
        end else begin
            my_packed_array[0] = 8'h0;
            my_packed_array[1] = 8'h0;
            my_packed_array[2] = 8'h0;
            my_packed_array[3] = 8'h0;
        end
        my_packed_array[0][3:0] = inj_input_slice_pa_1755007854495_176;
    end
    assign inj_output_pa_1755007854495_252 = my_packed_array[3];
    assign inj_output_pa_element1_1755007854496_349 = my_packed_array[1];
    // END: module_packed_array_ts1755007854496

    assign inj_sum_1755007854495_933 = inj_a_1755007854495_263 + inj_b_1755007854495_188;
    // END: simple_adder_ts1755007854495
endmodule

