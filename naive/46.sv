module m_arith #(
    parameter WIDTH = 8
) (
    input  logic [WIDTH-1:0] in1,
    input  logic [WIDTH-1:0] in2,
    input  logic [1:0]       op_sel,
    output logic [WIDTH:0]   result
);
    always_comb begin
        unique case (op_sel)
            2'd0: result = in1 + in2;
            2'd1: result = in1 - in2;
            2'd2: result = {1'b0, in1 & in2};
            2'd3: result = {1'b0, in1 | in2};
            default: result = '0;
        endcase
    end
endmodule
module m_fsm (
    input  logic clk,
    input  logic rst,
    input  logic start,
    output logic busy
);
    typedef enum logic [1:0] {IDLE = 2'd0, BUSY = 2'd1, DONE = 2'd2} state_t;
    state_t state, nxt_state;
    always_comb begin
        nxt_state = state;
        case (state)
            IDLE: if (start) nxt_state = BUSY;
            BUSY: nxt_state = DONE;
            DONE: nxt_state = IDLE;
            default: nxt_state = IDLE;
        endcase
    end
    always_ff @(posedge clk or posedge rst) begin
        if (rst) state <= IDLE;
        else     state <= nxt_state;
    end
    assign busy = (state == BUSY);
endmodule
module m_struct (
    input  logic [3:0] a_in,
    input  logic [7:0] b_in,
    output logic [11:0] flat
);
    typedef struct packed {
        logic [3:0] a;
        logic [7:0] b;
    } s_t;
    s_t s_var;
    always_comb begin
        s_var.a = a_in;
        s_var.b = b_in;
        flat    = {s_var.a, s_var.b};
    end
endmodule
module m_generate #(
    parameter N = 4
) (
    input  logic [N-1:0] din,
    output logic [N-1:0] dout
);
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_rev
            assign dout[i] = din[N-1-i];
        end
    endgenerate
endmodule
module m_assert (
    input  logic clk,
    input  logic [3:0] sig,
    output logic ok
);
    property p_sig_not_all_one;
        @(posedge clk) sig != 4'hF;
    endproperty
    assert property (p_sig_not_all_one);
    always_comb ok = (sig != 4'hF);
endmodule
module m_class (
    input  logic [15:0] x,
    input  logic [15:0] y,
    output logic [31:0] prod
);
    class multiplier;
        function automatic int unsigned mult(int unsigned a, b);
            return a * b;
        endfunction
    endclass
    always_comb begin
        automatic multiplier m = new();
        prod = m.mult(x, y);
    end
endmodule
module m_function (
    input  logic [7:0] in_a,
    input  logic [7:0] in_b,
    output logic [15:0] out_c
);
    typedef logic [7:0] byte_t;
    function automatic byte_t add_bytes(byte_t a, byte_t b);
        add_bytes = a + b;
    endfunction
    task automatic widen_and_assign(input byte_t val, output logic [15:0] dst);
        dst = {8'h00, val};
    endtask
    byte_t sum_byte;
    always_comb begin
        sum_byte = add_bytes(in_a, in_b);
        widen_and_assign(sum_byte, out_c);
    end
endmodule
module m_union (
    input  logic [15:0] din,
    output logic [7:0]  high_byte
);
    typedef struct packed {
        logic [7:0] lo;
        logic [7:0] hi;
    } bytes_t;
    typedef union packed {
        logic [15:0] half;
        bytes_t      bytes;
    } u_t;
    u_t u_var;
    always_comb begin
        u_var.half = din;
        high_byte  = u_var.bytes.hi;
    end
endmodule
