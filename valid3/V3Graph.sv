module comb_chain #(
    parameter int WIDTH  = 8,
    parameter int STAGES = 16
) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    wire [WIDTH-1:0] stage [0:STAGES];
    assign stage[0] = in;
    genvar i;
    generate
        for (i = 0; i < STAGES; i++) begin
            assign stage[i+1] = {stage[i][WIDTH-2:0], stage[i][WIDTH-1]};
        end
    endgenerate
    assign out = stage[STAGES];
endmodule
module seq_chain #(
    parameter int WIDTH = 16,
    parameter int DEPTH = 4
) (
    input  logic                   clk,
    input  logic                   rst_n,
    input  logic [WIDTH-1:0]       din,
    output logic [WIDTH-1:0]       dout
);
    logic [WIDTH-1:0] regs [0:DEPTH-1];
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            int idx;
            for (idx = 0; idx < DEPTH; idx++) regs[idx] <= '0;
        end else begin
            int j;
            regs[0] <= din;
            for (j = 1; j < DEPTH; j++) regs[j] <= regs[j-1];
        end
    end
    assign dout = regs[DEPTH-1];
endmodule
module struct_array #(
    parameter int SIZE = 4
) (
    input  logic [SIZE-1:0] in,
    output logic [SIZE-1:0] out
);
    typedef struct packed {
        logic a;
        logic b;
    } pair_t;
    pair_t arr [SIZE-1:0];
    always_comb begin
        for (int k = 0; k < SIZE; k++) begin
            arr[k].a = in[k];
            arr[k].b = ~in[k];
            out[k]   = arr[k].a & arr[k].b;
        end
    end
endmodule
module class_counter #(
    parameter int WIDTH = 8
) (
    input  logic             clk,
    input  logic             rst,
    input  logic             enable,
    output logic [WIDTH-1:0] count_out
);
    class Cnt;
        int unsigned count;
    endclass
    Cnt c;
    initial begin
        c = new();
        c.count = 0;
    end
    always_ff @(posedge clk) begin
        if (rst) begin
            c.count <= 0;
        end else if (enable) begin
            c.count <= c.count + 1;
        end
        count_out <= c.count[WIDTH-1:0];
    end
endmodule
module function_array #(
    parameter int N = 8
) (
    input  logic [N-1:0] in,
    output logic [N-1:0] out
);
    function automatic logic [N-1:0] f (input logic [N-1:0] x);
        f = ~x + 1;
    endfunction
    assign out = f(in);
endmodule
module generate_tree #(
    parameter int F = 4
) (
    input  logic [F-1:0] a,
    output logic         y
);
    logic [F-1:0] tmp;
    always_comb begin
        for (int m = 0; m < F; m++) begin
            tmp[m] = (m % 2) ? ~a[m] : a[m];
        end
        y = &tmp;
    end
endmodule
module unique_case (
    input  logic [3:0] sel,
    input  logic       a,
    input  logic       b,
    input  logic       c,
    input  logic       d,
    output logic       y
);
    always_comb begin
        unique case (sel)
            4'd0:    y = a;
            4'd1:    y = b;
            4'd2:    y = c;
            4'd3:    y = d;
            default: y = 1'b0;
        endcase
    end
endmodule
module packed_union (
    input  logic [7:0] in,
    output logic [7:0] out
);
    typedef union packed {
        logic [7:0] as_byte;
        struct packed {
            logic [3:0] low;
            logic [3:0] high;
        } nibbles;
    } u_t;
    u_t u;
    always_comb begin
        u.as_byte = in;
        out       = {u.nibbles.high, u.nibbles.low};
    end
endmodule
module fanout_module #(
    parameter int F = 64
) (
    input  logic         in,
    output logic [F-1:0] out
);
    always_comb begin
        for (int i = 0; i < F; i++) begin
            out[i] = in;
        end
    end
endmodule
module enum_fsm (
    input  logic clk,
    input  logic rst_n,
    input  logic in,
    output logic out
);
    typedef enum logic [1:0] { S0 = 2'b00, S1 = 2'b01, S2 = 2'b10 } state_t;
    state_t state, next;
    always_comb begin
        unique case (state)
            S0:     next = in ? S1 : S0;
            S1:     next = in ? S2 : S0;
            S2:     next = S0;
            default next = S0;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) state <= S0;
        else        state <= next;
    end
    assign out = (state == S2);
endmodule
