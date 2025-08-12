module SignedConversionMod(
    input  logic [31:0] in_vec,
    output logic signed [31:0] out_signed
);
    assign out_signed = $signed(in_vec);
endmodule
module UnsignedConversionMod(
    input  logic signed [31:0] in_signed,
    output logic [31:0] out_unsigned
);
    assign out_unsigned = $unsigned(in_signed);
endmodule
module RtoiConversionMod(
    input  logic [63:0] real_bits_in,
    output logic signed [31:0] int_out
);
    real r;
    always_comb begin
        r       = $bitstoreal(real_bits_in);
        int_out = $rtoi(r);
    end
endmodule
module ItorConversionMod(
    input  logic signed [31:0] int_in,
    output logic [63:0] real_bits_out
);
    real r;
    always_comb begin
        r             = $itor(int_in);
        real_bits_out = $realtobits(r);
    end
endmodule
module RealToBitsConversionMod(
    input  logic [63:0] real_in_bits,
    output logic [63:0] real_out_bits
);
    real r;
    always_comb begin
        r            = $bitstoreal(real_in_bits);
        real_out_bits = $realtobits(r);
    end
endmodule
module BitsToRealConversionMod(
    input  logic [63:0] bits_in,
    output logic [63:0] bits_out
);
    real r;
    always_comb begin
        r        = $bitstoreal(bits_in);
        bits_out = $realtobits(r);
    end
endmodule
module ShortRealToBitsConversionMod(
    input  logic [31:0] dummy_in_bits,
    output logic [31:0] bits_out
);
    shortreal sr;
    always_comb begin
        sr       = $bitstoshortreal(dummy_in_bits);
        bits_out = $shortrealtobits(sr);
    end
endmodule
module BitsToShortRealConversionMod(
    input  logic [31:0] bits_in,
    output logic [31:0] bits_out
);
    shortreal sr;
    always_comb begin
        sr       = $bitstoshortreal(bits_in);
        bits_out = $shortrealtobits(sr);
    end
endmodule
