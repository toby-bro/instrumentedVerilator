package util_pkg;
    function automatic logic [31:0] add32(
        input logic [31:0] a,
        input logic [31:0] b
    );
        add32 = a + b;
    endfunction
endpackage
module complex_feature(
    input  logic [31:0] in0,
    input  logic [31:0] in1,
    input  logic [2:0]  index,
    input  logic        sel,
    output logic [31:0] out
);
    logic [31:0] mem [0:7];
    function automatic logic [31:0] mix(
        input logic [31:0] x,
        input logic [31:0] y
    );
        mix = (x & 32'hFFFF0000) | (y & 32'h0000FFFF);
    endfunction
    always_comb begin
        logic bit0;
        bit0 = in0[index];
        logic [15:0] part0;
        part0 = in1[31:16];
        logic [7:0] part1;
        part1 = in0[index +: 8];
        logic [31:0] mem_val;
        mem_val = mem[index];
        logic [31:0] concat_val;
        concat_val = {part0, part1};
        logic [31:0] temp;
        if (sel) begin
            temp = concat_val;
        end else begin
            temp = mem_val;
        end
        out = bit0 ? mix(temp, in1) : mix(in0, temp);
    end
endmodule
module fork_feature(
    input  logic       clk,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    always_ff @(posedge clk) begin
        automatic logic [7:0] up;
        automatic logic [7:0] down;
        fork
            up   = din + 8'd1;
            down = din - 8'd1;
        join
        dout <= up ^ down;
    end
endmodule
module pkgfunc_feature(
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] y
);
    import util_pkg::add32;
    always_comb begin
        y = add32(a, b);
    end
endmodule
