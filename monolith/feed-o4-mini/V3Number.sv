module bitwise_ops(
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] and_out,
    output logic [7:0] or_out,
    output logic [7:0] xor_out,
    output logic [7:0] not_out
);
    always_comb begin
        and_out = a & b;
        or_out  = a | b;
        xor_out = a ^ b;
        not_out = ~a;
    end
endmodule
module reduction_ops(
    input  logic [7:0] a,
    output logic       rnd_and,
    output logic       rnd_or,
    output logic       rnd_xor,
    output logic       rnd_nor
);
    always_comb begin
        rnd_and = &a;
        rnd_or  = |a;
        rnd_xor = ^a;
        rnd_nor = ~|a;
    end
endmodule
module concat_repl(
    input  logic [3:0] a,
    input  logic [1:0] b,
    output logic [7:0] out
);
    logic [3:0] brep2;
    always_comb begin
        brep2 = {b, b};
        out    = {brep2, a};
    end
endmodule
module slice_shift(
    input  logic signed [7:0] a,
    input  logic [2:0]        sh,
    output logic [3:0]        upper,
    output logic [3:0]        lower,
    output logic [7:0]        shl,
    output logic [7:0]        shr,
    output logic signed [7:0] sra
);
    always_comb begin
        upper = a[7:4];
        lower = a[3:0];
        shl   = a << sh;
        shr   = a >> sh;
        sra   = a >>> sh;
    end
endmodule
module arith_ops(
    input  logic [7:0]  x,
    input  logic [7:0]  y,
    output logic [7:0]  sum,
    output logic [7:0]  sub,
    output logic [15:0] mul,
    output logic [7:0]  divi,
    output logic [7:0]  modo
);
    always_comb begin
        sum  = x + y;
        sub  = x - y;
        mul  = x * y;
        divi = x / (y != 0 ? y : 1);
        modo = x % (y != 0 ? y : 1);
    end
endmodule
module count_and_log2(
    input  logic [15:0] val,
    output logic [4:0]  popcnt,
    output logic [4:0]  log2b
);
    integer i;
    always_comb begin
        popcnt = 0;
        log2b  = 0;
        for (i = 0; i < 16; i = i + 1) begin
            if (val[i]) popcnt = popcnt + 1;
            if (val[i]) log2b  = i;
        end
    end
endmodule
module four_state_ops(
    input  tri   [1:0] t,
    output logic     any_x,
    output logic     any_z,
    output logic     all_x,
    output logic     all_z
);
    always_comb begin
        any_x = (t[0] === 1'bx) || (t[1] === 1'bx);
        any_z = (t[0] === 1'bz) || (t[1] === 1'bz);
        all_x = (t[0] === 1'bx) && (t[1] === 1'bx);
        all_z = (t[0] === 1'bz) && (t[1] === 1'bz);
    end
endmodule
module gen_loop_ops(
    input  logic [7:0] in,
    output logic [7:0] out
);
    genvar idx;
    generate
        for (idx = 0; idx < 8; idx = idx + 1) begin : loop_assign
            assign out[idx] = in[idx];
        end
    endgenerate
endmodule
module param_example #(
    parameter int WIDTH = 4
)(
    input  logic [WIDTH-1:0] a,
    output logic [WIDTH-1:0] b
);
    assign b = { a[WIDTH-2:0], a[WIDTH-1] };
endmodule
module func_log2(
    input  logic [31:0] num,
    output logic [4:0]  out
);
    function automatic [4:0] my_log2(input logic [31:0] n);
        integer i;
        my_log2 = 0;
        for (i = 31; i >= 0; i = i - 1) begin
            if (n[i]) begin
                my_log2 = i;
                break;
            end
        end
    endfunction
    assign out = my_log2(num);
endmodule
