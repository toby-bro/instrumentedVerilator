module m_constant_x
(
    input  logic        sel,
    output logic [4:0]  y,
    output logic        case_eq,
    output logic        case_neq
);
    localparam logic [4:0] C_XZ = 5'b1x0z1;
    assign y = sel ? 5'bx1x01 : C_XZ;
    assign case_eq  = (y === C_XZ);
    assign case_neq = (y !== 5'bx1x01);
endmodule
module m_vector_sel
(
    input  logic        clk,
    input  logic [3:0]  idx,
    input  logic        bit_in,
    output logic        bit_out
);
    logic [7:0] vec;
    always_ff @(posedge clk) begin
        vec[idx] <= bit_in;
    end
    assign bit_out = vec[idx + 4'd1];
endmodule
module m_array_sel
(
    input  logic        clk,
    input  logic [4:0]  index,
    input  logic [7:0]  data_in,
    output logic [7:0]  data_out
);
    logic [7:0] mem [0:3];
    always_ff @(posedge clk) begin
        mem[index] <= data_in;
    end
    assign data_out = mem[index + 5'd1];
endmodule
module m_wildcard_compare
(
    input  logic [3:0]  a,
    input  logic [3:0]  b,
    output logic        eq_wild,
    output logic        neq_wild
);
    assign eq_wild  = (a ==? b);
    assign neq_wild = (a !=? 4'b1x0x);
endmodule
module m_unknown_and_countbits
(
    input  logic [7:0]  in_vec,
    output logic        is_unk,
    output logic [3:0]  cnt_bits
);
    assign is_unk = $isunknown(in_vec);
    assign cnt_bits = $countbits(in_vec, 2'b11, 2'bxx);
endmodule
