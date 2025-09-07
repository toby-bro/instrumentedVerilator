module split_if_empty_then (
    input logic clk_p,
    input logic condition_p,
    input logic [7:0] in_val_p,
    output logic [7:0] out_reg_p
);
    always @(posedge clk_p) begin
        if (condition_p) begin
        end else begin
            out_reg_p <= in_val_p;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_condition_p_1755007862546_358,
    input logic [7:0] inj_in_val_p_1755007862546_889,
    input wire reset,
    output logic [7:0] inj_out_reg_p_1755007862546_27
);
    split_if_empty_then split_if_empty_then_inst_1755007862546_2869 (
        .in_val_p(inj_in_val_p_1755007862546_889),
        .out_reg_p(inj_out_reg_p_1755007862546_27),
        .clk_p(clk),
        .condition_p(inj_condition_p_1755007862546_358)
    );
endmodule

