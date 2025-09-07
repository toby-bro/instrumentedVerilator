module m_logic_ops(
    input  logic [7:0] din,
    output logic       o_and,
    output logic       o_or,
    output logic       o_xor,
    output logic       o_red_and,
    output logic       o_red_or,
    output logic       o_red_xor
);
    assign o_and      = 1'b1 & din[0];
    assign o_or       = 1'b0 | din[1];
    assign o_xor      = din[2] ^ 1'b1;
    assign o_red_and  = &{din[3], din[4]};
    assign o_red_or   = |{din[5], din[6]};
    assign o_red_xor  = ^{din[7], din[0]};
endmodule
module m_shift_mask(
    input  logic [31:0] din,
    output logic [31:0] dout
);
    assign dout = 32'hFF & ((din << 24) | (din >> 24));
endmodule
module m_concat_rep(
    input  logic [3:0] a,
    output logic [7:0] y,
    output logic [3:0] z
);
    assign y = {2{a}};                 
    assign z = {a[3:2], a[1:0]};       
endmodule
module m_cond(
    input  logic [7:0] in,
    output logic [7:0] o1,
    output logic [7:0] o2
);
    assign o1 = (in == 8'd0) ? 8'hFF : in;   
    assign o2 = (in != 8'd0) ? in    : 8'h00;
endmodule
module m_pow(
    input  logic  [3:0] p,
    output logic [15:0] y
);
    assign y = 16'd2 ** p;   
endmodule
module m_pow2_ops(
    input  logic [15:0] in,
    output logic [15:0] out_shift,
    output logic [15:0] out_mul,
    output logic [15:0] out_div,
    output logic [15:0] out_mod
);
    assign out_shift = in << 3;        
    assign out_mul   = in * 16'd8;     
    assign out_div   = in / 16'd8;     
    assign out_mod   = in % 16'd8;     
endmodule
module m_wordsel(
    input  logic [127:0] data,
    output logic         bit64
);
    assign bit64 = data[64];           
endmodule
