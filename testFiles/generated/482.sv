module split_conditional_blocking (
    input logic condition_o,
    input logic [7:0] in_false_o,
    input logic [7:0] in_true_o,
    output logic [7:0] out_val_o
);
    always @(*) begin
        if (condition_o) begin
            out_val_o = in_true_o;
        end else begin
            out_val_o = in_false_o;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_condition_o_1755007915269_98,
    input logic [7:0] inj_in_false_o_1755007915269_970,
    input logic [7:0] inj_in_true_o_1755007915269_672,
    input wire reset,
    output logic [7:0] inj_out_val_o_1755007915269_592
);
    split_conditional_blocking split_conditional_blocking_inst_1755007915269_173 (
        .out_val_o(inj_out_val_o_1755007915269_592),
        .condition_o(inj_condition_o_1755007915269_98),
        .in_false_o(inj_in_false_o_1755007915269_970),
        .in_true_o(inj_in_true_o_1755007915269_672)
    );
endmodule

