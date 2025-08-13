module const_and_or (
    input  logic       in_bit,
    output logic       out_bit
);
    assign out_bit = (1'b1 & in_bit) | (1'b0 & in_bit);
endmodule
module shift_mask_or (
    input  logic [31:0] in_bus,
    output logic [7:0]  out_byte
);
    assign out_byte = 8'hFF & ( (in_bus << 8) | (in_bus >> 24) );
endmodule
module reduce_concat (
    input  logic [1:0] in_vec,
    output logic       out_and
);
    assign out_and = &{in_vec[0], in_vec[1]};
endmodule
module sel_over_concat (
    input  logic [3:0] in_bus,
    output logic [1:0] out_bits
);
    assign out_bits = {in_bus[1], in_bus[0]}[1:0];
endmodule
module xor_identical (
    input  logic [3:0] in_vec,
    output logic [3:0] out_vec
);
    assign out_vec = in_vec ^ in_vec;
endmodule
module mul_power_two (
    input  logic [7:0] in_byte,
    output logic [10:0] out_word
);
    assign out_word = in_byte * 8;
endmodule
module shift_and_split (
    input  logic [31:0] in_bus,
    output logic [31:0] out_bus
);
    assign out_bus = (in_bus & 32'h00FF00FF) << 8;
endmodule
module replicate_xor (
    input  logic        in_bit,
    output logic [7:0]  out_bus
);
    assign out_bus = {8{in_bit}} ^ 8'hAA;
endmodule
module cond_zero (
    input  logic        sel,
    input  logic [7:0]  a,
    output logic [7:0]  out_bus
);
    assign out_bus = sel ? a : 8'h00;
endmodule
