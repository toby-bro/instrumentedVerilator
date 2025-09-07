module child_module_v1_config_dummy (
    input logic i,
    output logic o
);
    assign o = ~i; 
endmodule

module split_basic_nonblocking (
    input logic clk_b,
    input logic [7:0] in2_a,
    output logic [7:0] out2_a
);
    always @(posedge clk_b) begin
        out2_a <= in2_a;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_i_1755007915955_279,
    input logic [7:0] inj_in2_a_1755007915955_557,
    input wire reset,
    output logic inj_o_1755007915955_474,
    output logic [7:0] inj_out2_a_1755007915955_644
);
    child_module_v1_config_dummy child_module_v1_config_dummy_inst_1755007915955_7785 (
        .i(inj_i_1755007915955_279),
        .o(inj_o_1755007915955_474)
    );
    split_basic_nonblocking split_basic_nonblocking_inst_1755007915955_2783 (
        .clk_b(clk),
        .in2_a(inj_in2_a_1755007915955_557),
        .out2_a(inj_out2_a_1755007915955_644)
    );
endmodule

