module mod_params #(parameter int WIDTH = 8, parameter signed [3:0] OFFSET = 3) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    localparam int MULT = WIDTH * 2;
    assign out = in + OFFSET + MULT;
endmodule
module mod_struct_union (
    input  logic [15:0] din,
    output logic        bit_a,
    output logic [6:0]  bits_b,
    output logic [7:0]  u_out
);
    typedef struct packed { logic a; logic [6:0] b; } my_struct_t;
    typedef union  packed { my_struct_t f; logic [7:0] u; } my_union_t;
    my_union_t myu;
    always_comb begin
        myu.u = din[7:0];
    end
    assign bit_a = myu.f.a;
    assign bits_b = myu.f.b;
    assign u_out = myu.u;
endmodule
module mod_memory (
    input  logic        clk,
    input  logic        wr,
    input  logic [3:0]  addr,
    input  logic [7:0]  din,
    output logic [7:0]  dout
);
    logic [7:0] mem [0:15];
    always_ff @(posedge clk) begin
        if (wr) mem[addr] <= din;
    end
    assign dout = mem[addr];
endmodule
module mod_generate #(parameter int N = 4) (
    input  logic [N-1:0] in,
    output logic [N-1:0] out
);
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : gen_xor
            assign out[i] = in[i] ^ 1'b1;
        end
    endgenerate
endmodule
module mod_class_inst (
    input  logic        clk,
    input  logic        rst,
    input  logic [7:0]  inc_val,
    output logic [7:0]  out
);
    class Counter;
        rand logic [7:0] value;
        function void inc();
            value = value + 1;
        endfunction
    endclass
    Counter c;
    always_ff @(posedge clk) begin
        if (rst) begin
            c = new();
            c.value = inc_val;
        end else begin
            c.inc();
        end
        out <= c.value;
    end
endmodule
module mod_function (
    input  logic [7:0] in,
    output logic [7:0] out
);
    function automatic logic [7:0] reverse_bits(input logic [7:0] din);
        int i;
        begin
            for (i = 0; i < 8; i = i + 1)
                reverse_bits[i] = din[7-i];
        end
    endfunction
    assign out = reverse_bits(in);
endmodule
module mod_generate_if #(parameter int SEL = 0) (
    input  logic [7:0] in0,
    input  logic [7:0] in1,
    input  logic [7:0] in2,
    output logic [7:0] out
);
    generate
        if (SEL == 0) begin : gen0
            assign out = in0;
        end else if (SEL == 1) begin : gen1
            assign out = in1;
        end else begin : gen2
            assign out = in2;
        end
    endgenerate
endmodule
module mod_enum (
    input  logic [1:0] s,
    output logic       done
);
    typedef enum logic [1:0] {IDLE = 2'd0, BUSY = 2'd1, DONE = 2'd2} state_t;
    state_t state;
    always_comb begin
        state = state_t'(s);
    end
    assign done = (state == DONE);
endmodule
