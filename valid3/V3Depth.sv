module deep_unary_expr(
    input  logic [31:0] in1,
    input  logic [31:0] in2,
    output logic [31:0] out1
);
    always_comb begin : PROC_DEEP_UNARY
        out1 = ~~~~~~~~~~~~~~~~~(in1 + in2);
    end
endmodule
module task_mtask_expr(
    input  logic [31:0] data_in,
    output logic [31:0] data_out
);
    task automatic do_work(input logic [31:0] din, output logic [31:0] dout);
        logic [31:0] temp;
        temp = ((((((din + 32'd1)
                  * (din ^ 32'd3))
                  ^ (din << 2))
                  & (din | 32'd5))
                  + 32'd7)
                  ^ (din >> 4));
        dout = temp;
    endtask
    always_comb begin : PROC_TASK_CALL
        do_work(data_in, data_out);
    end
endmodule
module wide_concat_expr(
    input  logic [127:0] a,
    input  logic [127:0] b,
    output logic [255:0] y
);
    logic [511:0] wide_tmp;
    logic [511:0] shifted;
    always_comb begin
        wide_tmp = {2{{a,b}}};
        shifted  = wide_tmp >> 3;
        y        = shifted[255:0];
    end
endmodule
module nested_conditional_expr(
    input  logic [7:0]  sel,
    input  logic [31:0] d0,
    input  logic [31:0] d1,
    input  logic [31:0] d2,
    input  logic [31:0] d3,
    output logic [31:0] y
);
    assign y = sel[0] ? (sel[1] ? d0
                                : (sel[2] ? (sel[3] ? d2 : d3)
                                          : (sel[4] ? d1 : d0)))
                      : (sel[5] ? (sel[6] ? d2 : d3)
                                : (sel[7] ? d1 : d0));
endmodule
module function_deep_expr(
    input  logic [63:0] in_a,
    input  logic [63:0] in_b,
    output logic [63:0] out_c
);
    function automatic [63:0] heavy_func(input [63:0] x, input [63:0] y);
        heavy_func = ((((((x + y)
                        * (x ^ y))
                        + (~x))
                        ^ (~y))
                        & (x | y))
                        << 4)
                        + (x >> 3);
    endfunction
    assign out_c = heavy_func(in_a, in_b);
endmodule
