module literal_ops
  (input  logic         i,
   output logic [3:0]   o);
   localparam logic [3:0] L0  = '0;
   localparam logic [3:0] L1  = '1;
   localparam logic [3:0] LX  = 'x;
   localparam logic [3:0] LZ  = 'z;
   localparam logic [3:0] D   = 4'd10;
   localparam logic [3:0] B   = 4'b1010;
   localparam logic [3:0] O   = 4'o12;
   localparam logic [3:0] H   = 4'hA;
   localparam logic [3:0] COMB = (L0 | L1) ^ (B & O) ^~ H;
   assign o = COMB ^ {3'b000,i};
endmodule
module arith_large #(parameter int W = 128)
  (input  logic [W-1:0] a,
   output logic [W-1:0] o);
   localparam logic [W-1:0] CONST_A = {W{1'b1}};
   localparam logic [W-1:0] CONST_B = CONST_A >> 3;
   localparam logic [W-1:0] MUL_R   = CONST_A * CONST_B;
   localparam logic [W-1:0] DIV_R   = CONST_A / 17;
   localparam logic [W-1:0] MOD_R   = CONST_A % 17;
   localparam logic [W-1:0] POW_R   = CONST_B ** 4;
   localparam logic [W-1:0] RES     = (MUL_R ^ DIV_R) + MOD_R + POW_R;
   assign o = RES ^ a;
endmodule
module shift_ops
  (input  logic  [31:0] in,
   output logic  [31:0] out);
   localparam logic [31:0] BASE = 32'hAA55AA55;
   localparam logic [31:0] SR   = BASE >> 5;
   localparam logic [31:0] SL   = BASE << 7;
   localparam logic signed [31:0] AR = $signed(BASE) >>> 3;
   localparam logic [31:0] RES  = SR ^ SL ^ AR;
   assign out = RES ^ in;
endmodule
module reduce_ops
  (input  logic  [7:0] in,
   output logic        out);
   localparam logic [7:0] V      = 8'hF0;
   localparam bit         REDAND = &V;
   localparam bit         REDOR  = |V;
   localparam bit         REDXOR = ^V;
   localparam bit         LOGNOT = !REDAND;
   assign out = REDOR ^ REDXOR ^ LOGNOT ^ in[0];
endmodule
module compare_ops
  (input  logic dummy,
   output logic res);
   localparam logic [15:0] A = 16'h1234;
   localparam logic [15:0] B = 16'h2345;
   localparam bit EQ      = (A == B);
   localparam bit NEQ     = (A != B);
   localparam bit G       = (A  >  B);
   localparam bit GE      = (A >=  B);
   localparam bit L       = (A  <  B);
   localparam bit LE      = (A <=  B);
   localparam bit WILDEQ  = (A ==? 16'h1xx4);
   localparam bit WILDNEQ = (A !=? 16'h1xx4);
   assign res = EQ | NEQ | G | GE | L | LE | WILDEQ | WILDNEQ | dummy;
endmodule
module string_ops
  (input  logic       dummy,
   output logic [7:0] ascii0);
   localparam string S1   = "HelloWorld";
   localparam int    LEN  = S1.len();
   localparam string S2   = S1.toupper();
   localparam string S3   = S2.tolower();
   localparam string S4   = S1.substr(1,3);
   localparam byte   C0   = S1[0];
   localparam string CAT  = {S4,S3};
   localparam bit    CMP  = (S1 < S2);
   assign ascii0 = C0;
endmodule
module count_ops
  (input  logic  [15:0] in,
   output logic  [7:0]  count);
   localparam logic [15:0] VAL   = 16'hA5A5;
   localparam int ONES           = $countones(VAL);
   localparam bit UNKNOWN_FLAG   = $isunknown(16'hx);
   localparam int CLOG           = $clog2(257);
   localparam int RESULT         = ONES + UNKNOWN_FLAG + CLOG;
   assign count = RESULT[7:0] ^ in[7:0];
endmodule
