module complex_logic_chain(
    input  logic        clk,
    input  logic [31:0] din,
    output logic [31:0] dout
);
    logic [31:0] stage0, stage1, stage2, stage3, stage4;
    always_ff @(posedge clk) begin
        stage0 <= din ^ 32'hA5A5A5A5;
    end
    always_comb begin
        stage1 = {stage0[15:0], stage0[31:16]};
    end
    always_ff @(posedge clk) begin
        stage2 <= stage1 + 32'h12345678;
    end
    always_comb begin
        stage3 = (stage2 << 3) | (stage2 >> 29);
    end
    always_ff @(posedge clk) begin
        stage4 <= stage3 ^ stage2;
    end
    assign dout = stage4;
endmodule
module dpi_logic(
    input  logic        clk,
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] y
);
    import "DPI-C" function int c_add (input int a, input int b);
    logic [31:0] res;
    always_ff @(posedge clk) begin
        res <= c_add(a, b);
    end
    assign y = res;
endmodule
module slice_writer(
    input  logic        clk,
    input  logic [15:0] in_lo,
    input  logic [15:0] in_hi,
    output logic [31:0] vector_out
);
    logic [31:0] vec;
    always_ff @(posedge clk) begin
        vec[15:0] <= in_lo;
    end
    always_ff @(posedge clk) begin
        vec[31:16] <= in_hi;
    end
    assign vector_out = vec;
endmodule
module big_array_logic(
    input  logic        clk,
    input  logic [7:0]  index,
    output logic [31:0] val
);
    logic [31:0] mem [0:255];
    always_ff @(posedge clk) begin
        mem[index] <= mem[index] + 1;
    end
    assign val = mem[index];
endmodule
module parallel_counter(
    input  logic clk,
    input  logic en,
    output logic [7:0] count_out
);
    logic [7:0] cnt1, cnt2;
    always_ff @(posedge clk) if (en) cnt1 <= cnt1 + 1;
    always_ff @(posedge clk) if (en) cnt2 <= cnt2 + cnt1;
    assign count_out = cnt2;
endmodule
module function_pipe(
    input  logic [15:0] in_data,
    output logic [15:0] out_data
);
    function automatic [15:0] f (input [15:0] x);
        f = (x << 1) ^ (x >> 1);
    endfunction
    assign out_data = f(in_data);
endmodule
