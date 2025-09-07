module graph_chain #(parameter DEPTH = 8) (
    input  logic [DEPTH-1:0] inp,
    output logic             outp
);
    logic [DEPTH-1:0] chain;
    genvar i;
    generate
        for (i = 0; i < DEPTH; i++) begin : g
            if (i == 0) begin
                always_comb chain[i] = inp[i];
            end else begin
                always_comb chain[i] = chain[i-1] ^ inp[i];
            end
        end
    endgenerate
    assign outp = ^chain;
endmodule
module graph_branching #(parameter W = 4) (
    input  logic [W-1:0] in_a,
    input  logic [W-1:0] in_b,
    output logic [W-1:0] out_y
);
    function automatic logic [W-1:0] mux (
        input logic              sel,
        input logic [W-1:0]      a,
        input logic [W-1:0]      b
    );
        mux = sel ? a : b;
    endfunction
    logic sel;
    always_comb sel   = ^in_a;
    always_comb out_y = mux(sel, in_a, in_b);
endmodule
module graph_struct (
    input  logic [7:0] d,
    output logic [7:0] q
);
    typedef struct packed {
        logic [3:0] lo;
        logic [3:0] hi;
    } s_t;
    s_t st_in, st_out;
    always_comb begin
        st_in.lo  = d[3:0];
        st_in.hi  = d[7:4];
        st_out.lo = st_in.hi;
        st_out.hi = st_in.lo;
    end
    assign q = {st_out.hi, st_out.lo};
endmodule
module graph_enum (
    input  logic clk,
    input  logic rst_n,
    input  logic a,
    output logic y
);
    typedef enum logic [1:0] {S0 = 2'd0, S1 = 2'd1, S2 = 2'd2} state_t;
    state_t state, next;
    always_comb begin
        unique case (state)
            S0:   next = a ? S1 : S0;
            S1:   next = a ? S2 : S0;
            default: next = S0;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) state <= S0;
        else        state <= next;
    end
    assign y = (state == S2);
endmodule
module graph_union (
    input  logic [31:0] in_data,
    output logic [31:0] out_data
);
    typedef union packed {
        logic [31:0] word;
        logic [7:0]  bytes[4];
    } u_t;
    u_t src, dst;
    always_comb begin
        src.word    = in_data;
        dst.bytes[0] = src.bytes[3];
        dst.bytes[1] = src.bytes[2];
        dst.bytes[2] = src.bytes[1];
        dst.bytes[3] = src.bytes[0];
    end
    assign out_data = dst.word;
endmodule
module graph_assert (
    input  logic clk,
    input  logic en,
    input  logic data,
    output logic pass
);
    logic last;
    always_ff @(posedge clk) last <= data;
    assign pass = (last === data);
    property p_cons;
        @(posedge clk) disable iff (!en) data == last;
    endproperty
    assert property(p_cons);
endmodule
module graph_array #(parameter DEPTH = 4) (
    input  logic [7:0] din [DEPTH],
    input  logic [1:0] sel,
    output logic [7:0] dout
);
    logic [7:0] pipe [DEPTH];
    genvar i;
    generate
        for (i = 0; i < DEPTH; i++) begin : ARR
            always_comb pipe[i] = din[i] + i;
        end
    endgenerate
    always_comb dout = pipe[sel];
endmodule
