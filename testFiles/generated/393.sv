module attributes_test (
    input logic i_attr_in,
    output logic o_attr_out
);
    (* synthesis_preserve *) logic internal_signal;
    always_comb begin : my_combinational_block
        internal_signal = i_attr_in ? 1'b1 : 1'b0;
        o_attr_out      = internal_signal;
    end
endmodule

module module_function (
    input wire [7:0] in_func_a,
    input wire [7:0] in_func_b,
    output logic [7:0] out_func_result
);
    function automatic [7:0] add_and_subtract;
    input [7:0] val1;
    input [7:0] val2;
    reg [7:0] temp;
    begin
    temp = val1 + val2;
    add_and_subtract = temp - 1;
    end
    endfunction
    always_comb begin
    out_func_result = add_and_subtract(in_func_a, in_func_b);
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_i_attr_in_1755007885975_430,
    input wire [7:0] inj_in_func_a_1755007885975_793,
    input wire [7:0] inj_in_func_b_1755007885975_991,
    input wire reset,
    output logic inj_o_attr_out_1755007885975_477,
    output logic [7:0] inj_out_func_result_1755007885975_559
);
    module_function module_function_inst_1755007885975_6478 (
        .in_func_a(inj_in_func_a_1755007885975_793),
        .in_func_b(inj_in_func_b_1755007885975_991),
        .out_func_result(inj_out_func_result_1755007885975_559)
    );
    attributes_test attributes_test_inst_1755007885975_4356 (
        .o_attr_out(inj_o_attr_out_1755007885975_477),
        .i_attr_in(inj_i_attr_in_1755007885975_430)
    );
endmodule

