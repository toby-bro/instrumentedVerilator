class Multiplier;
    function automatic int mult(input int a);
        mult = a * 2;
    endfunction
endclass
class RandHolder;
    rand int value;
endclass
module func_call_mod #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    function automatic logic [WIDTH-1:0] mix(
        input logic [WIDTH-1:0] a = '0,
        input logic [WIDTH-1:0] b = '0
    );
        mix = a ^ b;
    endfunction
    always_comb begin
        out = mix( , in );
    end
endmodule
module task_call_mod (
    input  logic clk,
    output logic done
);
    task automatic toggle();
        done = ~done;
    endtask
    always_ff @(posedge clk) begin
        toggle;
    end
endmodule
module system_call_mod (
    input  logic [15:0] in,
    output logic [4:0]  clog2_out
);
    always_comb begin
        clog2_out = $clog2(in + 1);
    end
endmodule
module class_call_mod (
    input  logic [31:0] in,
    output logic [31:0] out
);
    Multiplier m;
    always_comb begin
        if (m == null)
            m = new();
        out = m.mult(in);
    end
endmodule
module randomize_mod (
    input  logic [31:0] in,
    output logic [31:0] out
);
    RandHolder h;
    always_comb begin
        if (h == null)
            h = new();
        if (h.randomize() with { value == in; })
            out = h.value;
        else
            out = 32'd0;
    end
endmodule
module array_iter_mod (
    input  logic [31:0] in,
    output logic [31:0] out
);
    int arr[];
    int result;
    always_comb begin
        arr = '{1, 2, 3, 4, 5};
        result = arr.sum() with (item + in);
        out = result;
    end
endmodule
module named_arg_mod (
    input  logic [31:0] in,
    output logic [31:0] out
);
    function automatic int add(
        input int a,
        input int b,
        input int c = 5
    );
        add = a + b + c;
    endfunction
    always_comb begin
        out = add(.c(), .b(in), .a(2));
    end
endmodule
