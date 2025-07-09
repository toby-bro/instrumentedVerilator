module func_args_test #(
    parameter WIDTH = 8
) (
    input  logic [WIDTH-1:0] in_value,
    output logic [WIDTH-1:0] out_value
);
    function automatic logic [WIDTH-1:0] complex_op(
        input  logic [WIDTH-1:0] a,
        output logic [WIDTH-1:0] b,
        ref    logic [WIDTH-1:0] c,
        input  logic [3:0]        sel = 4'd15
    );
        logic [WIDTH-1:0] tmp;
        tmp = sel[0] ? (a + c) : (a ^ c);
        b   = tmp;
        c   = c + sel;
        complex_op = tmp;
    endfunction
    logic [WIDTH-1:0] side;
    logic [WIDTH-1:0] ignore;
    always_comb begin
        side      = in_value;
        out_value = complex_op(in_value, ignore, side);
    end
endmodule
module task_and_static (
    input  logic clk,
    output logic flag
);
    function static int simple_add(input int a, input int b);
        simple_add = a + b;
    endfunction
    task automatic modify(ref int target);
        target = simple_add(target, 1);
    endtask
    int counter;
    always_ff @(posedge clk) begin
        modify(counter);
        flag <= counter[0];
    end
endmodule
module dpi_import_example (
    input  logic [31:0] a_in,
    input  logic [31:0] b_in,
    output logic [31:0] sum_out
);
    import "DPI-C" context function int unsigned dpi_add(
        input int unsigned a,
        input int unsigned b
    );
    int unsigned tmp_sum;
    always_comb begin
        tmp_sum = dpi_add(a_in, b_in);
        sum_out = tmp_sum[31:0];
    end
endmodule
module prototype_example (
    input  logic [7:0] data_in,
    output logic [7:0] data_out
);
    class transform_cls;
        extern static function logic [7:0] transform(input logic [7:0] d);
    endclass
    function logic [7:0] transform_cls::transform(input logic [7:0] d);
        transform = ~d;
    endfunction
    assign data_out = transform_cls::transform(data_in);
endmodule
