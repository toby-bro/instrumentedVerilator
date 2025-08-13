module unroll_basic(
    input  logic [7:0]  in,
    output logic [15:0] out
);
    always_comb begin
        int i;
        logic [15:0] acc;
        acc = 0;
        for (i = 0; i < 8; i = i + 1) begin
            acc = acc + in;
        end
        out = acc;
    end
endmodule
module gen_loop_mod(
    input  logic        dummy,
    output logic [31:0] out_vec
);
    genvar g;
    generate
        for (g = 0; g < 4; g = g + 1) begin : gen_blk
            localparam [7:0] GENVAL = g;
            assign out_vec[g*8 +: 8] = GENVAL;
        end
    endgenerate
endmodule
module while_loop_mod(
    input  logic [3:0] in,
    output logic [3:0] out
);
    always_comb begin
        int cnt;
        cnt = 0;
        while (cnt < 4) begin
            cnt = cnt + 1;
        end
        out = cnt;
    end
endmodule
module unroll_disable_mod(
    input  logic [3:0] in,
    output logic [7:0] out
);
    always_comb begin
        int i;
        logic [7:0] acc;
        acc = 0;
        for (i = 0; i < 16; i = i + 1) begin
            acc = acc + in;
        end
        out = acc;
    end
endmodule
module unroll_full_param_mod#(
    parameter WIDTH = 8
)(
    input  logic [WIDTH-1:0] in,
    output logic             parity
);
    always_comb begin
        int idx;
        logic p;
        p = 0;
        for (idx = 0; idx < WIDTH; idx = idx + 1) begin
            p = p ^ in[idx];
        end
        parity = p;
    end
endmodule
module nested_loop_mod(
    input  logic [3:0] in,
    output logic [7:0] out
);
    always_comb begin
        int i, j;
        logic [7:0] acc;
        acc = 0;
        for (i = 0; i < 4; i = i + 1) begin
            for (j = 0; j < 2; j = j + 1) begin
                acc = acc + (in << i);
            end
        end
        out = acc;
    end
endmodule
module modify_iter_mod(
    input  logic [3:0] in,
    output logic [3:0] out
);
    always_comb begin
        int i;
        logic [3:0] acc;
        acc = 0;
        for (i = 0; i < 4; i = i + 1) begin
            i = i;          
            acc = acc + in;
        end
        out = acc;
    end
endmodule
module large_loop_mod(
    input  logic [7:0]  in,
    output logic [15:0] out
);
    always_comb begin
        int i;
        logic [15:0] acc;
        acc = 0;
        for (i = 0; i < 64; i = i + 1) begin
            acc = acc + in;
        end
        out = acc;
    end
endmodule
