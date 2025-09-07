module split_conditional_nb (
    input logic clk_d,
    input logic condition_d,
    input logic [7:0] in_false_d,
    input logic [7:0] in_true_d,
    output logic [7:0] out_reg_d
);
    always @(posedge clk_d) begin
        if (condition_d) begin
            out_reg_d <= in_true_d;
        end else begin
            out_reg_d <= in_false_d;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_condition_d_1755007816382_955,
    input logic [7:0] inj_in_false_d_1755007816382_286,
    input logic [7:0] inj_in_true_d_1755007816382_408,
    input wire reset,
    output logic [7:0] inj_out_reg_d_1755007816382_98
);
    split_conditional_nb split_conditional_nb_inst_1755007816382_7418 (
        .out_reg_d(inj_out_reg_d_1755007816382_98),
        .clk_d(clk),
        .condition_d(inj_condition_d_1755007816382_955),
        .in_false_d(inj_in_false_d_1755007816382_286),
        .in_true_d(inj_in_true_d_1755007816382_408)
    );
endmodule

