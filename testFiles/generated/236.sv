module split_nested_if (
    input logic clk_m,
    input logic cond1_m,
    input logic cond2_m,
    input logic [7:0] val_a_m,
    input logic [7:0] val_b_m,
    input logic [7:0] val_c_m,
    output logic [7:0] result_m
);
    always @(posedge clk_m) begin
        if (cond1_m) begin
            if (cond2_m) begin
                result_m <= val_a_m;
            end else begin
                result_m <= val_b_m;
            end
        end else begin
            result_m <= val_c_m;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_cond1_m_1755007833111_385,
    input logic inj_cond2_m_1755007833111_134,
    input logic [7:0] inj_val_a_m_1755007833111_412,
    input logic [7:0] inj_val_b_m_1755007833111_922,
    input logic [7:0] inj_val_c_m_1755007833111_128,
    input wire reset,
    output logic [7:0] inj_result_m_1755007833111_661
);
    split_nested_if split_nested_if_inst_1755007833111_4089 (
        .val_c_m(inj_val_c_m_1755007833111_128),
        .result_m(inj_result_m_1755007833111_661),
        .clk_m(clk),
        .cond1_m(inj_cond1_m_1755007833111_385),
        .cond2_m(inj_cond2_m_1755007833111_134),
        .val_a_m(inj_val_a_m_1755007833111_412),
        .val_b_m(inj_val_b_m_1755007833111_922)
    );
endmodule

