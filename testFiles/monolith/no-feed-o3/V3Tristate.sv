module tri_inout_assign (
    input  logic en,
    input  logic din,
    inout  tri   tri_sig,
    output logic dout
);
    assign tri_sig = en ? din : 1'bz;
    assign dout    = tri_sig;
endmodule
module bufif1_mod (
    input  wire d,
    input  wire en,
    output wire q
);
    bufif1 g1 (q, d, en);
endmodule
module bufif0_mod (
    input  wire d,
    input  wire en,
    output wire q
);
    bufif0 g0 (q, d, en);
endmodule
module pull_primitive_mod (
    input  wire sel,
    output wire q
);
    wire w_up, w_down;
    pullup   (w_up);
    pulldown (w_down);
    assign q = sel ? w_up : w_down;
endmodule
module wired_or_mod (
    input  wire a,
    input  wire b,
    output wire y
);
    wor w;
    assign w = a;
    assign w = b;
    assign y = w;
endmodule
module strength_assign_mod (
    input  wire d,
    output wire q
);
    wire w;
    assign (strong1, weak0) w = d;
    assign q = w;
endmodule
module logic_z_mod (
    input  wire a,
    output wire y
);
    assign y = (a & 1'bz) | (a | 1'bz);
endmodule
module case_eq_z_mod (
    input  logic a,
    output logic y
);
    assign y = (a === 1'bz) ? 1'b1 : 1'b0;
endmodule
module concat_sel_z_mod (
    input  logic [3:0] din,
    output logic [1:0] dout
);
    assign dout = {din[3], 1'bz};
endmodule
module countones_mod (
    input  logic [7:0] din,
    output logic [3:0] count
);
    assign count = $countones(din);
endmodule
