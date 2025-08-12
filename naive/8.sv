module parity_calc (
    input  logic [7:0] data_i,
    output logic       parity_o
);
    always_comb begin
        parity_o = ^data_i;
    end
endmodule
module fifo_queue #(
    parameter int DEPTH = 4,
    parameter int WIDTH = 8
) (
    input  logic                 clk_i,
    input  logic                 rst_ni,
    input  logic                 push_i,
    input  logic [WIDTH-1:0]     data_i,
    input  logic                 pop_i,
    output logic [WIDTH-1:0]     data_o,
    output logic                 empty_o,
    output logic                 full_o
);
    logic [WIDTH-1:0] mem [DEPTH-1:0];
    logic [$clog2(DEPTH):0] wptr, rptr, cnt;
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            wptr <= 0;
            rptr <= 0;
            cnt  <= 0;
        end else begin
            if (push_i && !full_o) begin
                mem[wptr] <= data_i;
                wptr      <= (wptr + 1) % DEPTH;
                cnt       <= cnt + 1;
            end
            if (pop_i && !empty_o) begin
                rptr <= (rptr + 1) % DEPTH;
                cnt  <= cnt - 1;
            end
        end
    end
    assign data_o  = mem[rptr];
    assign empty_o = (cnt == 0);
    assign full_o  = (cnt == DEPTH);
endmodule
module class_example (
    input  logic        sel_i,
    input  logic [15:0] a_i,
    input  logic [15:0] b_i,
    output logic [15:0] y_o
);
    class adder;
        function automatic logic [15:0] add (logic [15:0] x, logic [15:0] y);
            add = x + y;
        endfunction
    endclass
    always_comb begin
        adder ad;
        ad = new();
        if (sel_i)
            y_o = ad.add(a_i, b_i);
        else
            y_o = ad.add(a_i, ~b_i);
    end
endmodule
module gen_and #(
    parameter int WIDTH = 16
) (
    input  logic [WIDTH-1:0] a_i,
    input  logic [WIDTH-1:0] b_i,
    output logic [WIDTH-1:0] y_o
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : and_loop
            assign y_o[i] = a_i[i] & b_i[i];
        end
    endgenerate
endmodule
module bus_mux (
    input  logic [1:0]  sel_i,
    input  logic [31:0] a_i,
    input  logic [31:0] b_i,
    input  logic [31:0] c_i,
    input  logic [31:0] d_i,
    output logic [31:0] y_o
);
    typedef enum logic [1:0] { SEL_A = 2'd0, SEL_B = 2'd1, SEL_C = 2'd2, SEL_D = 2'd3 } sel_t;
    typedef struct packed { logic [31:0] data; } bus_t;
    bus_t bus_a, bus_b, bus_c, bus_d, bus_y;
    always_comb begin
        bus_a.data = a_i;
        bus_b.data = b_i;
        bus_c.data = c_i;
        bus_d.data = d_i;
        unique case (sel_t'(sel_i))
            SEL_A : bus_y = bus_a;
            SEL_B : bus_y = bus_b;
            SEL_C : bus_y = bus_c;
            default: bus_y = bus_d;
        endcase
    end
    assign y_o = bus_y.data;
endmodule
module endian_swap #(
    parameter int WIDTH = 32
) (
    input  logic [WIDTH-1:0] data_i,
    output logic [WIDTH-1:0] data_o
);
    typedef union {
        logic [WIDTH-1:0] word;
        byte              bytes[WIDTH/8];
    } u_t;
    u_t in_u, out_u;
    integer idx;
    always_comb begin
        in_u.word = data_i;
        for (idx = 0; idx < WIDTH/8; idx++) begin
            out_u.bytes[idx] = in_u.bytes[WIDTH/8 - 1 - idx];
        end
        data_o = out_u.word;
    end
endmodule
module safe_counter #(
    parameter int MAX_VAL = 255
) (
    input  logic                             clk_i,
    input  logic                             rst_ni,
    input  logic                             en_i,
    output logic [$clog2(MAX_VAL+1)-1:0]     cnt_o
);
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni)
            cnt_o <= '0;
        else if (en_i)
            cnt_o <= (cnt_o == MAX_VAL) ? '0 : cnt_o + 1;
    end
    assert property (@(posedge clk_i) disable iff (!rst_ni) cnt_o <= MAX_VAL);
endmodule
