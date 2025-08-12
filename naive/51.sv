module mod_param_arith #(
    parameter WIDTH = 8
) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    assign out = in + {{(WIDTH-1){1'b0}},1'b1};
endmodule
module mod_struct (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [4:0] sum
);
    typedef struct packed {
        logic [3:0] x;
        logic [3:0] y;
    } pair_t;
    pair_t p;
    always_comb begin
        p.x = a;
        p.y = b;
        sum = p.x + p.y;
    end
endmodule
module mod_union (
    input  logic [7:0] in,
    output logic [3:0] hi,
    output logic [3:0] lo
);
    typedef union packed {
        logic [7:0] bv;
        struct packed {
            logic [3:0] h;
            logic [3:0] l;
        } parts;
    } u_t;
    u_t uvar;
    always_comb begin
        uvar.bv = in;
        hi = uvar.parts.h;
        lo = uvar.parts.l;
    end
endmodule
module mod_enum_ff (
    input  logic       clk,
    input  logic       rst,
    output logic [1:0] state
);
    typedef enum logic [1:0] {S0 = 2'b00, S1 = 2'b01, S2 = 2'b10} state_t;
    state_t curr;
    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            curr <= S0;
        else
            curr <= (curr == S0) ? S1 :
                    (curr == S1) ? S2 : S0;
    end
    assign state = curr;
endmodule
module mod_generate_array #(
    parameter N = 4
) (
    input  logic [N-1:0] in,
    output logic [N-1:0] out
);
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : gen_loop
            assign out[i] = ~in[i];
        end
    endgenerate
endmodule
module mod_memory (
    input  logic [7:0] addr,
    input  logic       wr,
    input  logic [7:0] wdata,
    output logic [7:0] rdata
);
    logic [7:0] mem [0:255];
    always_comb begin
        if (wr)
            mem[addr] = wdata;
        rdata = mem[addr];
    end
endmodule
module mod_class (
    input  logic in,
    output logic out
);
    class C;
        function logic calc(input logic x);
            calc = ~x;
        endfunction
    endclass
    always_comb begin
        static C c = new();
        out = c.calc(in);
    end
endmodule
module mod_queue_assoc (
    input  logic [3:0] key_in,
    output logic [3:0] q_out,
    output logic [7:0] assoc_out
);
    always_comb begin
        logic [3:0] q[$];
        int assoc[int];
        q.push_back(key_in);
        q_out = q.pop_front();
        assoc[key_in] = key_in * 2;
        assoc_out = assoc[key_in];
    end
endmodule
module mod_typedef_enum_inside (
    input  logic [2:0] a,
    output logic       valid
);
    typedef enum logic [1:0] {E0 = 2'b00, E1 = 2'b01, E2 = 2'b10, E3 = 2'b11} e_t;
    e_t evar;
    always_comb begin
        case (a)
            3'd0: evar = E0;
            3'd1: evar = E1;
            3'd2: evar = E2;
            default: evar = E3;
        endcase
        valid = (evar == E3) ? 1'b0 : 1'b1;
    end
endmodule
