module tri_bus(
    input  logic [7:0] din,
    input  logic       en,
    inout  wire  [7:0] bus,
    output logic [7:0] dout
);
    assign bus  = en ? din : 8'bz;
    assign dout = bus;
endmodule
module pull_example(
    input  logic in_sig,
    output logic out_sig
);
    wire w_pull;
    pullup(w_pull);
    assign out_sig = w_pull & in_sig;
endmodule
module strength_example(
    input  logic in_sig,
    output wire  out_sig
);
    wire w_strength;
    assign (strong1,weak0) w_strength = in_sig;
    assign out_sig = w_strength;
endmodule
module wired_example(
    input  logic a,
    input  logic b,
    output logic y_and,
    output logic y_or
);
    wand w_and;
    wor  w_or;
    assign w_and = a;
    assign w_and = b;
    assign w_or  = a;
    assign w_or  = b;
    assign y_and = w_and;
    assign y_or  = w_or;
endmodule
module bufif_example(
    input  logic data,
    input  logic enable,
    output wire  y
);
    wire t;
    bufif1(t,data,enable);
    assign y = t;
endmodule
module countones_example(
    input  logic [7:0] in_bus,
    output logic [4:0] cnt
);
    assign cnt = $countones(in_bus);
endmodule
module caseeq_example(
    input  logic [3:0] in_sig,
    output logic       eq,
    output logic       neq
);
    assign eq  = (in_sig === 4'bzzzz);
    assign neq = (in_sig !== 4'bzzzz);
endmodule
module concat_sel_example(
    input  logic [3:0] a,
    input  logic [3:0] b,
    input  logic       sel,
    output logic [3:0] y
);
    assign y = sel ? {a[2:0],1'bz} : {1'bz,b[3:1]};
endmodule
module triand_example(
    input  logic a,
    input  logic b,
    output logic y
);
    triand t_and_net;
    assign t_and_net = a;
    assign t_and_net = b;
    assign y = t_and_net;
endmodule
module tri_defaults(
    input  logic dummy_in,
    output logic pull_one,
    output logic pull_zero
);
    tri1 sig1;
    tri0 sig0;
    assign pull_one  = sig1;
    assign pull_zero = sig0 ^ dummy_in;
endmodule
