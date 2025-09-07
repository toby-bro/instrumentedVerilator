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

module split_conditional_reorder (
    input logic clk_cc,
    input logic condition_cc,
    input logic [7:0] val1_cc,
    input logic [7:0] val2_cc,
    input logic [7:0] val3_cc,
    output logic [7:0] out_reg_cc
);
    always @(posedge clk_cc) begin
        out_reg_cc <= val1_cc;
        if (condition_cc) begin
            out_reg_cc <= val2_cc;
        end else begin
            out_reg_cc <= val3_cc;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_condition_cc_1755007840362_527,
    input logic [7:0] inj_val1_cc_1755007840362_261,
    input logic [7:0] inj_val2_cc_1755007840362_822,
    input logic [7:0] inj_val3_cc_1755007840362_450,
    input wire reset,
    output logic inj_o_attr_out_1755007840362_243,
    output logic [7:0] inj_out_reg_cc_1755007840362_139
);
    attributes_test attributes_test_inst_1755007840362_385 (
        .o_attr_out(inj_o_attr_out_1755007840362_243),
        .i_attr_in(inj_condition_cc_1755007840362_527)
    );
    split_conditional_reorder split_conditional_reorder_inst_1755007840362_4451 (
        .out_reg_cc(inj_out_reg_cc_1755007840362_139),
        .clk_cc(clk),
        .condition_cc(inj_condition_cc_1755007840362_527),
        .val1_cc(inj_val1_cc_1755007840362_261),
        .val2_cc(inj_val2_cc_1755007840362_822),
        .val3_cc(inj_val3_cc_1755007840362_450)
    );
endmodule

