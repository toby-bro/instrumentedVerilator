module mod_clog2 #(parameter int WIDTH = 16) (
    input  logic [WIDTH-1:0] din,
    output logic [$clog2(WIDTH)-1:0] dout
);
    assign dout = din[$clog2(WIDTH)-1:0];
endmodule
module mod_countbits (
    input  logic [15:0] din,
    output logic [31:0] count_all
);
    assign count_all = $countbits(din, 1'b0, 1'b1, 1'bx, 1'bz);
endmodule
module mod_countones (
    input  logic [31:0] din,
    output logic [31:0] count_ones
);
    assign count_ones = $countones(din);
endmodule
module mod_boolean_bv (
    input  logic [7:0] din,
    output logic       flag_onehot,
    output logic       flag_onehot0,
    output logic       flag_unknown
);
    assign flag_onehot  = $onehot(din);
    assign flag_onehot0 = $onehot0(din);
    assign flag_unknown = $isunknown(din);
endmodule
module mod_realmath1 (
    input  real rin,
    output real rout
);
    always_comb begin
        real v1,  v2,  v3,  v4,  v5,  v6,  v7,  v8,  v9;
        real v10, v11, v12, v13, v14, v15, v16, v17, v18;
        v1  = $ln(rin + 1.0);
        v2  = $log10(rin + 1.0);
        v3  = $exp(rin);
        v4  = $sqrt(rin * rin + 1.0);
        v5  = $floor(rin);
        v6  = $ceil(rin);
        v7  = $sin(rin);
        v8  = $cos(rin);
        v9  = $tan(rin);
        v10 = $asin($tanh(rin));
        v11 = $acos($tanh(rin));
        v12 = $atan(rin);
        v13 = $sinh(rin);
        v14 = $cosh(rin);
        v15 = $tanh(rin);
        v16 = $asinh(rin);
        v17 = $acosh(rin + 1.0);
        v18 = $atanh($tanh(rin));
        rout = v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9 +
               v10 + v11 + v12 + v13 + v14 + v15 + v16 + v17 + v18;
    end
endmodule
module mod_realmath2 (
    input  real a,
    input  real b,
    output real rout
);
    always_comb begin
        real p, ang, hyp;
        p   = $pow(a, b);
        ang = $atan2(a, b);
        hyp = $hypot(a, b);
        rout = p + ang + hyp;
    end
endmodule
