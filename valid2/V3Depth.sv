module deep_expr_mod #(parameter int DEPTH = 64) (
    input  logic [31:0] in,
    output logic [31:0] out
);
    localparam int _unused = DEPTH;
    always_comb begin
        out = ((((((((in + in))))))));
    end
endmodule
module wide_op_mod (
    input  logic [1023:0] in,
    output logic [1023:0] out
);
    logic [2047:0] tmp;
    always_comb begin
        tmp = {in, in};
        out = tmp[1023:0] ^ (in >> 10);
    end
endmodule
module mtask_mod (
    input  logic       clk,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    logic [7:0] reg1;
    logic [7:0] reg2;
    always_ff @(posedge clk) begin
        fork
            reg1 <= din;
            reg2 <= reg1;
        join
        dout <= reg2;
    end
endmodule
import "DPI-C" function int my_c_func (input int a);
module dpi_mod (
    input  logic [31:0] in,
    output logic [31:0] out
);
    always_comb begin
        out = my_c_func(int'(in));
    end
endmodule
class simple_class;
    function automatic int add (input int a, b);
        return a + b;
    endfunction
endclass
module class_mod (
    input  logic [31:0] in,
    output logic [31:0] out
);
    simple_class c;
    always_comb begin
        c = new();
        out = c.add(int'(in), int'(in));
    end
endmodule
