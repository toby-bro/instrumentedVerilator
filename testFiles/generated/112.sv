module simple_logic_a (
    input wire data_a,
    output wire data_b
);
    assign data_b = ~data_a;
endmodule

module split_diff_vars_branches (
    input logic clk_z,
    input logic condition_z,
    input logic [7:0] in1_z,
    input logic [7:0] in2_z,
    output logic [7:0] out1_z,
    output logic [7:0] out2_z
);
    always @(posedge clk_z) begin
        if (condition_z) begin
            out1_z <= in1_z;
        end else begin
            out2_z <= in2_z;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_condition_z_1755007790128_403,
    input logic [7:0] inj_in1_z_1755007790128_526,
    input logic [7:0] inj_in2_z_1755007790128_975,
    input wire reset,
    output wire inj_data_b_1755007790128_166,
    output logic [7:0] inj_out1_z_1755007790128_680,
    output logic [7:0] inj_out2_z_1755007790128_696
);
    split_diff_vars_branches split_diff_vars_branches_inst_1755007790128_116 (
        .clk_z(clk),
        .condition_z(inj_condition_z_1755007790128_403),
        .in1_z(inj_in1_z_1755007790128_526),
        .in2_z(inj_in2_z_1755007790128_975),
        .out1_z(inj_out1_z_1755007790128_680),
        .out2_z(inj_out2_z_1755007790128_696)
    );
    simple_logic_a simple_logic_a_inst_1755007790128_8832 (
        .data_b(inj_data_b_1755007790128_166),
        .data_a(reset)
    );
endmodule

