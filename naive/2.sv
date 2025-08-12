module comb_logic_mod (
    input  logic [7:0] in_a,
    input  logic [7:0] in_b,
    output logic [7:0] out_y
);
    assign out_y = in_a ^ in_b;
endmodule
module param_gen_mod #(
    parameter int WIDTH = 16
) (
    input  logic [WIDTH-1:0] din,
    output logic [WIDTH-1:0] dout
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : GEN_REV
            assign dout[i] = din[WIDTH-1-i];
        end
    endgenerate
endmodule
module enum_fsm_mod (
    input  logic clk,
    input  logic rst_n,
    input  logic start,
    output logic done
);
    typedef enum logic [1:0] { IDLE, BUSY, FINISH } state_e;
    state_e state, nxt_state;
    always_comb begin
        nxt_state = state;
        unique case (state)
            IDLE   : if (start) nxt_state = BUSY;
            BUSY   :            nxt_state = FINISH;
            FINISH :            nxt_state = IDLE;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= nxt_state;
    end
    assign done = (state == FINISH);
endmodule
module struct_union_mod (
    input  logic [31:0] in_word,
    output logic [15:0] out_half
);
    typedef struct packed {
        logic [15:0] lo;
        logic [15:0] hi;
    } word_s;
    typedef union packed {
        word_s          word;
        logic [31:0]    flat;
    } word_u;
    word_u u;
    always_comb begin
        u.flat   = in_word;
        out_half = u.word.lo ^ u.word.hi;
    end
endmodule
module queue_array_mod (
    input  logic       clk,
    input  logic       rst_n,
    input  logic       wr_en,
    input  logic       rd_en,
    input  logic [7:0] wdata,
    output logic [7:0] rdata,
    output logic       empty
);
    logic [7:0] q[$];
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            q.delete();
            rdata <= 8'd0;
        end else begin
            if (wr_en)
                q.push_back(wdata);
            if (rd_en && (q.size() > 0))
                rdata <= q.pop_front();
        end
    end
    assign empty = (q.size() == 0);
endmodule
module class_usage_mod (
    input  logic       clk,
    input  logic       rst_n,
    input  logic [15:0] in_val,
    output logic [15:0] out_val
);
    class math_c;
        function int unsigned square (input int unsigned x);
            return x * x;
        endfunction
    endclass
    math_c hndl;
    logic  init;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            init    <= 1'b0;
            out_val <= 16'd0;
        end else begin
            if (!init) begin
                hndl = new();
                init <= 1'b1;
            end
            out_val <= hndl.square(in_val[7:0]);
        end
    end
endmodule
module assertions_mod (
    input  logic clk,
    input  logic rst_n,
    input  logic enable,
    output logic good
);
    logic prev_en;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            prev_en <= 1'b0;
        else
            prev_en <= enable;
    end
    property enable_sticky;
        @(posedge clk) disable iff (!rst_n)
        prev_en |-> enable;
    endproperty
    assert property (enable_sticky);
    assign good = enable;
endmodule
