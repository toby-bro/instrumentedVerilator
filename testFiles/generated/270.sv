module more_procedural (
    input logic [31:0] p_in1,
    input logic [31:0] p_in2,
    input logic [1:0] p_mode,
    output logic [31:0] p_out
);
    always_comb begin
        case (p_mode)
            2'b00: p_out = (p_in1 + p_in2) * 2;
            2'b01: p_out = (p_in1 - p_in2) / 3; 
            2'b10: p_out = (p_in1 << 4) | (p_in2 >> 2);
            default: p_out = ~(p_in1 ^ p_in2) + 1;
        endcase
    end
endmodule

module snippet (
    input wire clk,
    input logic [31:0] inj_p_in1_1755007844801_590,
    input logic [31:0] inj_p_in2_1755007844801_623,
    input logic [1:0] inj_p_mode_1755007844801_908,
    input wire reset,
    output logic [31:0] inj_p_out_1755007844801_218
);
    more_procedural more_procedural_inst_1755007844801_8356 (
        .p_mode(inj_p_mode_1755007844801_908),
        .p_out(inj_p_out_1755007844801_218),
        .p_in1(inj_p_in1_1755007844801_590),
        .p_in2(inj_p_in2_1755007844801_623)
    );
endmodule

