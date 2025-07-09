module conv_signed_unsigned
    #(parameter int WIDTH = 16)
    (
        input  logic [WIDTH-1:0] in_val,
        output logic signed [WIDTH-1:0] signed_out,
        output logic [WIDTH-1:0]         unsigned_out
    );
    localparam signed [7:0] CONST_SIGNED   = $signed(8'sd12);
    localparam        [7:0] CONST_UNSIGNED = $unsigned(8'sd12);
    always_comb begin
        signed_out   = $signed(in_val);
        unsigned_out = $unsigned(in_val);
    end
endmodule
module conv_rtoi_bitstoreal
    (
        input  logic [63:0] real_bits_in,
        output logic signed [31:0] int_out
    );
    localparam logic signed [31:0] CONST_RTOI = $rtoi(6.28);
    localparam real                CONST_B2R  = $bitstoreal(64'h3FF0000000000000);
    always_comb begin
        int_out = $rtoi($bitstoreal(real_bits_in));
    end
endmodule
module conv_itor_realtobits
    (
        input  logic signed [31:0] int_in,
        output logic [63:0]        real_bits_out
    );
    localparam logic [63:0] CONST_ITOR_R2B = $realtobits($itor(42));
    always_comb begin
        real_bits_out = $realtobits($itor(int_in));
    end
endmodule
module conv_shortreal_bits_roundtrip
    (
        input  logic [31:0] shortreal_bits_in,
        output logic [31:0] shortreal_bits_out
    );
    localparam logic [31:0] CONST_SR2B = $shortrealtobits(1.0);
    localparam shortreal    CONST_B2SR = $bitstoshortreal(32'h3F800000);
    always_comb begin
        shortreal_bits_out = $shortrealtobits($bitstoshortreal(shortreal_bits_in));
    end
endmodule
