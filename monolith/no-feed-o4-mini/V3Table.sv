module concat_mod (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [7:0] c
);
    assign c = {a, b};
endmodule
module array_sel_mod (
    input  logic [3:0] idx,
    output logic [7:0] val
);
    wire [7:0] mem [0:15];
    always_comb
        val = mem[idx];
endmodule
module assign_mod (
    input  logic [7:0] x,
    input  logic [7:0] y,
    output logic [7:0] z
);
    always_comb begin
        z = x & y;
    end
endmodule
module if_and_mod (
    input  logic        clk,
    input  logic        rst,
    input  logic [3:0]  in,
    output logic [3:0]  out
);
    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            out <= 4'b0;
        else if (in[0] & in[1])
            out <= in;
        else
            out <= in >> 1;
    end
endmodule
module delay_assign_mod (
    input  logic        clk,
    input  logic        en,
    input  logic [7:0]  d,
    output logic [7:0]  q
);
    always_ff @(posedge clk) begin
        if (en)
            q <= d;
        else
            q <= q;
    end
endmodule
module big_logic_mod (
    input  logic [4:0] in,
    output logic [4:0] out
);
    integer i;
    always_comb begin
        out = '0;
        for (i = 0; i < 5; i = i + 1) begin
            if (in[i])
                out[i] = i;
            else
                out[i] = 5;
        end
    end
endmodule
module func_mod (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [4:0] sum
);
    function logic [4:0] add4(input logic [3:0] x, input logic [3:0] y);
        add4 = x + y;
    endfunction
    always_comb
        sum = add4(a, b);
endmodule
module struct_mod (
    input  logic       sel,
    input  logic [7:0] d0,
    input  logic [7:0] d1,
    output logic [7:0] out
);
    typedef struct packed {
        logic [3:0] hi;
        logic [3:0] lo;
    } half_t;
    half_t h;
    always_comb begin
        h.hi = sel ? d1[7:4] : d0[7:4];
        h.lo = sel ? d1[3:0] : d0[3:0];
        out  = {h.hi, h.lo};
    end
endmodule
module enum_mod (
    input  logic [1:0] state_in,
    output logic       next_go
);
    typedef enum logic [1:0] {S0 = 2'b00, S1 = 2'b01, S2 = 2'b10} state_t;
    state_t state;
    always_comb begin
        state   = state_in;
        next_go = (state == S1) & (state != S2);
    end
endmodule
module typedef_mod (
    input  logic [7:0] in,
    output logic [7:0] out
);
    typedef logic [7:0] byte_t;
    byte_t x;
    always_comb
        x = in;
    assign out = x;
endmodule
