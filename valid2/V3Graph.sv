module graph_chain #(parameter N = 8) (
    input  logic [N-1:0] in,
    output logic         out
);
    logic [N:0] acc;
    assign acc[0] = ^in;
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : g_acc
            assign acc[i+1] = acc[i] ^ in[i];
        end
    endgenerate
    assign out = acc[N];
endmodule
module graph_mux (
    input  logic [3:0]  sel,
    input  logic [7:0]  a,
    input  logic [7:0]  b,
    input  logic [7:0]  c,
    input  logic [7:0]  d,
    output logic [7:0]  y
);
    always_comb begin
        unique case (sel)
            4'h0:   y = a;
            4'h1:   y = b;
            4'h2:   y = c;
            default:y = d;
        endcase
    end
endmodule
module graph_state_machine (
    input  logic clk,
    input  logic reset,
    input  logic trigger,
    output logic active
);
    typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;
    state_t state;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= IDLE;
        end else begin
            unique case (state)
                IDLE: if (trigger) state <= RUN;
                RUN:               state <= DONE;
                DONE:              state <= IDLE;
            endcase
        end
    end
    assign active = (state == RUN);
endmodule
module graph_struct_union (
    input  logic [31:0] bus_in,
    output logic [31:0] bus_out
);
    typedef struct packed {
        logic [7:0] byte0;
        logic [7:0] byte1;
        logic [7:0] byte2;
        logic [7:0] byte3;
    } bytes_t;
    typedef union packed {
        logic  [31:0] word;
        bytes_t       bytes;
    } data_u;
    data_u din, dout;
    always_comb begin
        din.word         = bus_in;
        dout.word        = 32'h0;
        dout.bytes.byte0 = din.bytes.byte3;
        dout.bytes.byte1 = din.bytes.byte2;
        dout.bytes.byte2 = din.bytes.byte1;
        dout.bytes.byte3 = din.bytes.byte0;
    end
    assign bus_out = dout.word;
endmodule
module graph_generate #(
    parameter W     = 4,
    parameter DEPTH = 4
) (
    input  logic [W-1:0] in_bus,
    output logic [W-1:0] out_bus
);
    logic [W-1:0] stage [0:DEPTH];
    assign stage[0] = in_bus;
    genvar k;
    generate
        for (k = 0; k < DEPTH; k++) begin : shift_stages
            assign stage[k+1] = {stage[k][W-2:0], stage[k][W-1]};
        end
    endgenerate
    assign out_bus = stage[DEPTH];
endmodule
module graph_logic_function (
    input  logic [15:0] a,
    input  logic [15:0] b,
    output logic [15:0] y
);
    function automatic [15:0] add_and_rotate (input [15:0] x, input [15:0] y_in);
        add_and_rotate = {x[14:0], 1'b0} + y_in;
    endfunction
    assign y = add_and_rotate(a, b) ^ (a & b);
endmodule
module graph_priority_if (
    input  logic [7:0] din,
    output logic [2:0] pos
);
    always_comb begin
        pos = 3'd0;
        if      (din[7]) pos = 3'd7;
        else if (din[6]) pos = 3'd6;
        else if (din[5]) pos = 3'd5;
        else if (din[4]) pos = 3'd4;
        else if (din[3]) pos = 3'd3;
        else if (din[2]) pos = 3'd2;
        else if (din[1]) pos = 3'd1;
        else if (din[0]) pos = 3'd0;
    end
endmodule
module graph_array_math #(
    parameter WIDTH = 8,
    parameter SIZE  = 4
) (
    input  logic [WIDTH-1:0] a   [SIZE],
    input  logic [WIDTH-1:0] b   [SIZE],
    output logic [WIDTH-1:0] sum [SIZE]
);
    genvar i;
    generate
        for (i = 0; i < SIZE; i++) begin : add_loop
            assign sum[i] = a[i] + b[i];
        end
    endgenerate
endmodule
module graph_latch (
    input  logic en,
    input  logic d,
    output logic q
);
    always_latch begin
        if (en) q <= d;
    end
endmodule
