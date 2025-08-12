module func_clog2 #(parameter int WIDTH = 16) (
    input  logic [WIDTH-1:0] din,
    output logic [WIDTH-1:0] dout
);
    localparam int CLOG2_WIDTH = $clog2(WIDTH);
    assign dout = din >> CLOG2_WIDTH;
endmodule
module func_countbits (
    input  logic [7:0]  din,
    output logic [31:0] dout
);
    localparam int CNT1 = $countbits(8'hA5, 1'b1);
    localparam int CNT0 = $countbits(8'hA5, 1'b0);
    localparam int CNTX = $countbits(8'bxxxxxxxx, 1'bx);
    localparam int CNTZ = $countbits(8'bzzzzzzzz, 1'bz);
    assign dout = $countbits(din, 1'b1) + CNT1 + CNT0 + CNTX + CNTZ;
endmodule
module func_countones (
    input  logic [15:0] din,
    output logic [31:0] dout
);
    localparam int CONST_ONES = $countones(16'hF00F);
    assign dout = $countones(din) + CONST_ONES;
endmodule
module func_boolean (
    input  logic [7:0] din,
    output logic [2:0] dout
);
    localparam bit ONEHOT_CONST  = $onehot (8'b0001_0000);
    localparam bit ONEHOT0_CONST = $onehot0(8'b0);
    localparam bit ISUNK_CONST   = $isunknown(8'bx1);
    assign dout[0] = $onehot (din);
    assign dout[1] = $onehot0(din);
    assign dout[2] = $isunknown({din[7:1], 1'bx}) ^ ONEHOT_CONST ^ ONEHOT0_CONST ^ ISUNK_CONST;
endmodule
module func_real1 (
    input  logic        dummy_in,
    output logic [31:0] dout
);
    localparam real V_LN      = $ln     (2.718281828);
    localparam real V_LOG10   = $log10  (1000.0);
    localparam real V_EXP     = $exp    (1.0);
    localparam real V_SQRT    = $sqrt   (16.0);
    localparam real V_FLOOR   = $floor  (3.7);
    localparam real V_CEIL    = $ceil   (3.2);
    localparam real V_SIN     = $sin    (0.0);
    localparam real V_COS     = $cos    (0.0);
    localparam real V_TAN     = $tan    (0.0);
    localparam real V_ASIN    = $asin   (1.0);
    localparam real V_ACOS    = $acos   (1.0);
    localparam real V_ATAN    = $atan   (1.0);
    localparam real V_SINH    = $sinh   (0.0);
    localparam real V_COSH    = $cosh   (0.0);
    localparam real V_TANH    = $tanh   (0.0);
    localparam real V_ASINH   = $asinh  (1.0);
    localparam real V_ACOSH   = $acosh  (2.0);
    localparam real V_ATANH   = $atanh  (0.5);
    localparam int INT_SUM = int'(
        V_LN   + V_LOG10 + V_EXP   + V_SQRT  + V_FLOOR + V_CEIL +
        V_SIN  + V_COS   + V_TAN   + V_ASIN  + V_ACOS  + V_ATAN +
        V_SINH + V_COSH  + V_TANH  + V_ASINH + V_ACOSH + V_ATANH
    );
    assign dout = INT_SUM[31:0];
endmodule
module func_real2 (
    input  logic        dummy_in,
    output logic [31:0] dout
);
    localparam real V_POW   = $pow  (2.0, 8.0);
    localparam real V_ATAN2 = $atan2(1.0, 1.0);
    localparam real V_HYPOT = $hypot(3.0, 4.0);
    localparam int INT_COMB = int'(V_POW + V_ATAN2 + V_HYPOT);
    assign dout = INT_COMB[31:0];
endmodule
