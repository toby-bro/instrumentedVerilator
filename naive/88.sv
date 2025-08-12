typedef logic [7:0] byte_t;
module param_mod #(parameter WIDTH = 8, parameter SUM = WIDTH + 4) (
    input  logic [WIDTH-1:0] in,
    output logic [SUM-1:0]   out
);
    assign out = {in, {4{1'b1}}};
endmodule
module comb_mod (
    input  logic a,
    input  logic b,
    input  logic c,
    output logic y
);
    always_comb begin
        if (a)
            y = b & c;
        else
            y = b | c;
    end
endmodule
module seq_mod (
    input  logic       clk,
    input  logic       rst,
    input  logic [3:0] d,
    output logic [3:0] q
);
    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            q <= 4'h0;
        else
            q <= d;
    end
endmodule
module array_mod (
    input  logic [3:0] inarr [1:0],
    output logic [4:0] outsum
);
    assign outsum = inarr[0] + inarr[1];
endmodule
module struct_union_mod (
    input  logic [3:0] in,
    output logic       out_a,
    output logic [2:0] out_b,
    output logic [3:0] out_raw
);
    typedef struct packed {
        logic       a;
        logic [2:0] b;
    } mystruct_t;
    typedef union packed {
        mystruct_t  s;
        logic [3:0] raw;
    } myunion_t;
    myunion_t u;
    always_comb begin
        u.raw   = in;
        out_a   = u.s.a;
        out_b   = u.s.b;
        out_raw = u.raw;
    end
endmodule
module function_mod (
    input  logic [3:0] in,
    output logic [3:0] out
);
    function logic [3:0] f(input logic [3:0] x);
        f = {x[2:0], ^x};
    endfunction
    always_comb out = f(in);
endmodule
module generate_mod #(parameter N = 4) (
    input  logic [N-1:0] in,
    output logic [N-1:0] out
);
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin
            assign out[i] = in[i] ^ in[(i+1) % N];
        end
    endgenerate
endmodule
module nested_generate #(parameter M = 2, parameter N = 3) (
    input  logic [M-1:0] in1,
    input  logic [N-1:0] in2,
    output logic [M*N-1:0] out
);
    genvar i, j;
    generate
        for (i = 0; i < M; i = i + 1) begin
            for (j = 0; j < N; j = j + 1) begin
                assign out[i*N + j] = in1[i] & in2[j];
            end
        end
    endgenerate
endmodule
module typedef_mod (
    input  byte_t in,
    output byte_t out
);
    assign out = ~in;
endmodule
