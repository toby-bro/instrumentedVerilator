module mod_arith(input  logic [7:0] a, b,
                 output logic [7:0] sum,
                 output logic [7:0] diff,
                 output logic [15:0] prod,
                 output logic [7:0] quot,
                 output logic [7:0] rem);
  assign sum  = a + b;
  assign diff = a - b;
  assign prod = a * b;
  assign quot = a / b;
  assign rem  = a % b;
endmodule
module mod_bitwise(input  logic [7:0] a, b,
                   output logic [7:0] and_o,
                   output logic [7:0] or_o,
                   output logic [7:0] xor_o,
                   output logic [7:0] not_a);
  assign and_o = a & b;
  assign or_o  = a | b;
  assign xor_o = a ^ b;
  assign not_a = ~a;
endmodule
module mod_reduce(input  logic [3:0] in,
                  output logic        red_and,
                  output logic        red_or,
                  output logic        red_xor);
  assign red_and = &in;
  assign red_or  = |in;
  assign red_xor = ^in;
endmodule
module mod_shift(input  logic [7:0] in,
                 input  logic [2:0] sh,
                 output logic [7:0] shl,
                 output logic [7:0] shr);
  assign shl = in << sh;
  assign shr = in >> sh;
endmodule
module mod_conditional(input  logic       sel,
                       input  logic [7:0] x, y,
                       output logic [7:0] out);
  assign out = sel ? x : y;
endmodule
module mod_concat_rep(input  logic [3:0] a, b,
                       output logic [7:0] concat_out,
                       output logic [15:0] rep4);
  assign concat_out = {a, b};
  assign rep4       = {4{a[0]}};
endmodule
module mod_select(input  logic [7:0] a,
                  output logic       bit0,
                  output logic [2:0] bits3_1);
  assign bit0    = a[0];
  assign bits3_1 = a[3:1];
endmodule
module mod_cast(input  logic signed [7:0] a,
                input  logic [7:0]        b,
                output logic signed [7:0] out_s,
                output logic [7:0]        out_u);
  assign out_s = $signed(a);
  assign out_u = $unsigned(b);
endmodule
module mod_sysfunc(input  logic [15:0] a,
                   output logic [4:0]  o_clog2,
                   output logic [4:0]  o_count1);
  assign o_clog2   = $clog2(a);
  assign o_count1  = $countones(a);
endmodule
module mod_cntzeros(input  logic [15:0] a,
                    output logic [4:0]  o_count0);
  assign o_count0 = $countones(~a);
endmodule
module mod_combo(input  logic [7:0] a, b,
                 input  logic [2:0] c,
                 output logic [7:0] out);
  assign out = ((a + b*2) & {8{c[0]}}) ^ {8{^(a | b)}};
endmodule
