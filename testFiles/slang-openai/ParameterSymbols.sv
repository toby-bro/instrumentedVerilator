class dummy;
    int v;
    function new();
        v = 0;
    endfunction
endclass
module basic_params_mod #(
    parameter int A     = 4,
    parameter int WIDTH = A + 4
) (
    input  logic               in,
    output logic [WIDTH-1:0]   out
);
    assign out = {WIDTH{in}};
endmodule
module implicit_string_mod #(
    parameter P_STR   = "hello",
    parameter int LEN = 5
) (
    input  logic in,
    output logic out
);
    assign out = in;
endmodule
module type_param_mod #(
    parameter type T      = int,
    parameter T   DEFAULT = T'(0)
) (
    input  T in,
    output T out
);
    assign out = in + DEFAULT;
endmodule
module child_defparam #(
    parameter bit P = 1
) (
    input  logic i,
    output logic o
);
    assign o = i ^ P;
endmodule
module parent_defparam (
    input  logic i,
    output logic o
);
    child_defparam inst1 ( .i(i), .o(o) );
    defparam inst1.P = 1'b0;
endmodule
module base_override #(
    parameter int WIDTH = 8
) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    assign out = in;
endmodule
module override_parent (
    input  logic [3:0] in,
    output logic [3:0] out
);
    base_override #(.WIDTH(4)) i0 ( .in(in), .out(out) );
endmodule
module specparam_mod (
    input  wire in,
    output wire out
);
    specify
        specparam PATHPULSE$in$out = (3, 6);
        specparam t_PD             = 2;
        (in => out) = t_PD;
    endspecify
    assign out = in;
endmodule
module default_expr_mod #(
    parameter int X = 5,
    parameter int Y = X + 2
) (
    input  logic         in,
    output logic [Y-1:0] out
);
    assign out = {Y{in}};
endmodule
module class_inst_mod #(
    parameter int DUMMY = 0
) (
    input  logic in,
    output logic out
);
    dummy d;
    always_comb begin
        d = new();
        out = in;
    end
endmodule
