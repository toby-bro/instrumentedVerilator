module chain_path #(parameter WIDTH = 8) (
    input  logic                 clk,
    input  logic [WIDTH-1:0]     din,
    output logic [WIDTH-1:0]     dout
);
    logic [WIDTH-1:0] stage0, stage1, stage2;
    always_ff @(posedge clk) stage0 <= din;
    always_ff @(posedge clk) stage1 <= stage0 + 1;
    always_ff @(posedge clk) stage2 <= stage1 ^ stage0;
    assign dout = stage2;
endmodule
module comb_path (
    input  logic [7:0] a,
    output logic [7:0] y
);
    logic [7:0] b, c, d, e;
    always_comb b = a + 1;
    always_comb c = b & ~a;
    always_comb d = c | b;
    always_comb e = {d[3:0], c[7:4]};
    assign y = e;
endmodule
module generated_chain #(parameter SIZE = 4) (
    input  logic [SIZE-1:0] din,
    output logic [SIZE-1:0] dout
);
    logic [SIZE-1:0] arr [0:SIZE-1];
    genvar i;
    generate
        for (i = 0; i < SIZE; ++i) begin : g
            if (i == 0) begin : first
                always_comb arr[i] = din;
            end
            else begin : rest
                always_comb arr[i] = arr[i-1] ^ din;
            end
        end
    endgenerate
    assign dout = arr[SIZE-1];
endmodule
module task_graph (
    input  logic clk,
    input  logic rst,
    input  logic in_sig,
    output logic out_sig
);
    logic state;
    task automatic update_state(input logic v);
        state <= v;
    endtask
    always_ff @(posedge clk) begin
        if (rst)
            state <= 1'b0;
        else
            update_state(in_sig);
    end
    assign out_sig = state;
endmodule
module struct_graph (
    input  logic [3:0] in_data,
    output logic [7:0] out_data
);
    typedef struct packed {
        logic [3:0] lo;
        logic [3:0] hi;
    } pair_t;
    pair_t s;
    always_comb begin
        s.lo = in_data;
        s.hi = ~in_data;
    end
    assign out_data = {s.hi, s.lo};
endmodule
module array_graph (
    input  logic [7:0] in0,
    input  logic [7:0] in1,
    output logic [7:0] out_sum
);
    typedef logic [7:0] byte_t;
    byte_t mem [0:1];
    always_comb begin
        mem[0] = in0;
        mem[1] = in1;
    end
    assign out_sum = mem[0] + mem[1];
endmodule
module enum_graph (
    input  logic [2:0] in_bits,
    output logic [2:0] out_bits
);
    typedef enum logic [1:0] {S0 = 2'd0, S1 = 2'd1, S2 = 2'd2} state_t;
    state_t s;
    always_comb begin
        case (in_bits[1:0])
            2'd0: s = S0;
            2'd1: s = S1;
            default: s = S2;
        endcase
    end
    assign out_bits = {1'b0, s};
endmodule
