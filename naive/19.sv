class parity_checker;
    function automatic logic even_parity(input logic [7:0] v);
        even_parity = ^v;
    endfunction
endclass
module arithmetic_unit #(parameter WIDTH = 32)
(
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    input  logic             sel,
    output logic [WIDTH-1:0] y
);
    function automatic logic [WIDTH-1:0] add(input logic [WIDTH-1:0] x,
                                             input logic [WIDTH-1:0] y_in);
        add = x + y_in;
    endfunction
    function automatic logic [WIDTH-1:0] sub(input logic [WIDTH-1:0] x,
                                             input logic [WIDTH-1:0] y_in);
        sub = x - y_in;
    endfunction
    always_comb begin
        if (sel)
            y = add(a, b);
        else
            y = sub(a, b);
    end
endmodule
module state_machine
(
    input  logic clk,
    input  logic rst,
    input  logic in_signal,
    output logic out_signal
);
    typedef enum logic [1:0] {S0, S1, S2} state_t;
    state_t state, next;
    always_comb begin
        next = state;
        case (state)
            S0: if (in_signal) next = S1;
            S1: if (in_signal) next = S2; else next = S0;
            S2: if (!in_signal) next = S0;
            default: next = S0;
        endcase
        out_signal = (state == S2);
    end
    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            state <= S0;
        else
            state <= next;
        assert (!(state == S2 && in_signal));
    end
endmodule
module struct_example
(
    input  logic [15:0] data_in,
    output logic [16:0] result
);
    typedef struct packed {
        logic [7:0] lo;
        logic [7:0] hi;
    } bytes_t;
    bytes_t s;
    always_comb begin
        s = data_in;
        result = {1'b0, s.lo} + {1'b0, s.hi};
    end
endmodule
module class_example
(
    input  logic [7:0] vector_in,
    output logic       parity
);
    parity_checker pc;
    always_comb begin
        pc = new();
        parity = pc.even_parity(vector_in);
    end
endmodule
module generate_example #(parameter N = 4)
(
    input  logic [N-1:0] in_bus,
    output logic [N-1:0] out_bus
);
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_block
            if (i % 2 == 0) begin : even
                always_comb out_bus[i] = ~in_bus[i];
            end else begin : odd
                always_comb out_bus[i] =  in_bus[i];
            end
        end
    endgenerate
endmodule
module union_example
(
    input  logic [31:0] raw,
    output logic [15:0] word0,
    output logic [15:0] word1
);
    typedef union packed {
        logic [31:0] as32;
        struct packed {
            logic [15:0] w0;
            logic [15:0] w1;
        } as16;
    } uword_t;
    uword_t u;
    always_comb begin
        u.as32 = raw;
        word0  = u.as16.w0;
        word1  = u.as16.w1;
    end
endmodule
