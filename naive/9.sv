module adder_mod #(parameter int WIDTH = 8)
(
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH  :0] sum
);
    typedef struct packed {
        logic [WIDTH-1:0] lhs;
        logic [WIDTH-1:0] rhs;
    } pair_t;
    class adder_cls;
        function automatic logic [WIDTH:0] add (input logic [WIDTH-1:0] x,
                                                input logic [WIDTH-1:0] y);
            add = x + y;
        endfunction
    endclass
    always_comb begin
        pair_t p;
        static adder_cls helper = new();
        p.lhs = a;
        p.rhs = b;
        sum   = helper.add(p.lhs, p.rhs);
    end
endmodule
module fsm_mod
(
    input  logic clk,
    input  logic reset_n,
    input  logic in_sig,
    output logic [1:0] state_o
);
    typedef enum logic [1:0] {IDLE = 2'd0, BUSY = 2'd1, DONE = 2'd2} state_t;
    state_t state, next_state;
    class fsm_helper;
        function automatic state_t advance (state_t s, logic in_val);
            case (s)
                IDLE : advance = in_val ? BUSY : IDLE;
                BUSY : advance = in_val ? BUSY : DONE;
                DONE : advance = IDLE;
                default: advance = IDLE;
            endcase
        endfunction
    endclass
    always_comb begin
        static fsm_helper h = new();
        next_state = h.advance(state, in_sig);
    end
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            state <= IDLE;
        else
            state <= next_state;
    end
    assign state_o = state;
endmodule
module array_mod #(parameter int DEPTH = 4, parameter int WIDTH = 16)
(
    input  logic [WIDTH-1:0] in_vec [0:DEPTH-1],
    output logic [WIDTH-1:0] out_sum
);
    integer i;
    always_comb begin
        out_sum = '0;
        for (i = 0; i < DEPTH; i++) begin
            out_sum += in_vec[i];
        end
    end
endmodule
module bitfield_mod
(
    input  logic [31:0] data_in,
    output logic [7:0]  byte3
);
    typedef struct packed {
        logic [7:0] b0;
        logic [7:0] b1;
        logic [7:0] b2;
        logic [7:0] b3;
    } word_s;
    always_comb begin
        word_s w;
        w = word_s'(data_in);
        byte3 = w.b3;
    end
endmodule
