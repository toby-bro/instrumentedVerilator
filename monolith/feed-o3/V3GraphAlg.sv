module redundant_edges_mod #(parameter WIDTH = 64)(
    input  logic [WIDTH-1:0] in_data,
    output logic [WIDTH-1:0] out_data
);
    logic [WIDTH-1:0] a_path;
    logic [WIDTH-1:0] b_path;
    logic [WIDTH-1:0] merge;
    assign a_path =  in_data;
    assign b_path =  in_data;
    assign merge  = (a_path & b_path) | (a_path ^ b_path);
    assign out_data = {merge[WIDTH-2:0], merge[WIDTH-1]};
endmodule
module transitive_edges_mod #(parameter WIDTH = 32)(
    input  logic [WIDTH-1:0] in_word,
    output logic [WIDTH-1:0] out_word
);
    logic [WIDTH-1:0] stage1, stage2, stage3;
    assign stage1 = in_word           ^ {WIDTH{1'b1}};
    assign stage2 = stage1            + in_word;
    assign stage3 = stage2            & stage1;
    assign out_word = (in_word | stage3) ^ stage2;
endmodule
module weakly_connected_mod #(parameter W0 = 8, parameter W1 = 16)(
    input  logic [W0-1:0]  in0,
    input  logic [W1-1:0]  in1,
    output logic [W0+W1-1:0] out_bus
);
    logic [W0-1:0] block_a [0:3];
    logic [W1-1:0] block_b [0:3];
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin : GEN_A
            if (i == 0) assign block_a[i] = in0;
            else        assign block_a[i] = block_a[i-1] + i;
        end
    endgenerate
    generate
        for (i = 0; i < 4; i++) begin : GEN_B
            if (i == 0) assign block_b[i] = in1;
            else        assign block_b[i] = block_b[i-1] ^ (i << 2);
        end
    endgenerate
    logic [W0+W1-1:0] bridge;
    assign bridge = {block_a[3], block_b[3]};
    assign out_bus = bridge;
endmodule
module strongly_connected_mod #(
    parameter WIDTH = 8
) (
    input  logic                  clk,
    input  logic                  rst,
    input  logic [WIDTH-1:0]      din,
    output logic [WIDTH-1:0]      dout
);
    logic [WIDTH-1:0] r0, r1, r2;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            r0 <= '0;
            r1 <= '0;
            r2 <= '0;
        end else begin
            r0 <= din;
            r1 <= r0 + din;        
            r2 <= r1 ^ r0;         
        end
    end
    assign dout = r2;
endmodule
module ranking_chain_mod #(
    parameter STAGES = 64
)(
    input  logic in_bit,
    output logic out_bit
);
    logic [STAGES:0] chain;
    assign chain[0] = in_bit;
    genvar idx;
    generate
        for (idx = 0; idx < STAGES; idx++) begin : GEN_CHAIN
            assign chain[idx+1] = chain[idx] ^ in_bit;
        end
    endgenerate
    assign out_bit = &chain;
endmodule
module sort_edges_mod #(
    parameter WIDTH = 16,
    parameter CHANNELS = 4
)(
    input  logic [WIDTH-1:0]  in_chan [CHANNELS-1:0],
    output logic [WIDTH-1:0]  out_mux
);
    logic [WIDTH-1:0] processed [CHANNELS-1:0];
    genvar c;
    generate
        for (c = 0; c < CHANNELS; c++) begin : GEN_PROC
            assign processed[c] = (in_chan[c] << c) + (in_chan[c] >> c);
        end
    endgenerate
    integer k;
    always_comb begin
        out_mux = '0;
        for (k = 0; k < CHANNELS; k++) begin
            if (processed[k] != '0) out_mux = processed[k];
        end
    end
endmodule
module parallelism_mod #(
    parameter WIDTH = 32,
    parameter UNITS = 8
)(
    input  logic [WIDTH-1:0] operands [UNITS-1:0],
    output logic [WIDTH-1:0] result
);
    logic [WIDTH-1:0] partial [UNITS-1:0];
    genvar u;
    generate
        for (u = 0; u < UNITS; u++) begin : GEN_UNIT
            assign partial[u] = operands[u] * (u + 1);
        end
    endgenerate
    logic [WIDTH-1:0] accumulator;
    integer t;
    always_comb begin
        accumulator = '0;
        for (t = 0; t < UNITS; t++) begin
            accumulator = accumulator + partial[t];
        end
        result = accumulator;
    end
endmodule
module subtree_loop_mod #(
    parameter WIDTH = 12
)(
    input  logic               clk,
    input  logic               rst_n,
    input  logic [WIDTH-1:0]   data_in,
    output logic [WIDTH-1:0]   data_out
);
    logic [WIDTH-1:0] acc_a, acc_b;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) acc_a <= '0;
        else        acc_a <= acc_b + data_in;
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) acc_b <= '0;
        else        acc_b <= acc_a ^ data_in;
    end
    assign data_out = (acc_a & acc_b) | (acc_a + acc_b);
endmodule
