module arith_unit (
    input  logic [7:0] in_a,
    input  logic [7:0] in_b,
    output logic [8:0] out_sum,
    output logic [7:0] out_diff
);
    typedef struct packed {
        logic [7:0] lo;
        logic       cin;
    } add_op_t;
    add_op_t op;
    always_comb begin
        op.lo   = in_a;
        op.cin  = 1'b0;
        out_sum = op.lo + in_b + op.cin;
        out_diff = in_a - in_b;
    end
endmodule
module shift_unit #(
    parameter WIDTH = 16,
    parameter SHIFT = 3
) (
    input  logic [WIDTH-1:0] din,
    output logic [WIDTH-1:0] dout
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : g
            if (i >= SHIFT) begin : gen_shift
                assign dout[i] = din[i - SHIFT];
            end else begin : gen_zero
                assign dout[i] = 1'b0;
            end
        end
    endgenerate
endmodule
module state_machine (
    input  logic clk,
    input  logic rst_n,
    input  logic in_toggle,
    output logic [1:0] state_out
);
    typedef enum logic [1:0] {IDLE = 2'd0, RUN = 2'd1, WAIT = 2'd2, DONE = 2'd3} state_t;
    state_t state, next_state;
    always_comb begin
        next_state = state;
        unique case (state)
            IDLE: if (in_toggle) next_state = RUN;
            RUN :               next_state = WAIT;
            WAIT:               next_state = DONE;
            DONE: if (!in_toggle) next_state = IDLE;
            default:            next_state = IDLE;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end
    assign state_out = state;
endmodule
module class_demo (
    input  logic [3:0] in_val,
    output logic [3:0] out_val
);
    class myadder;
        function automatic [3:0] add4 (input [3:0] x);
            return x + 4'd1;
        endfunction
    endclass
    myadder adder_h;
    always_comb begin
        if (adder_h == null) begin
            adder_h = new();
        end
        out_val = adder_h.add4(in_val);
    end
endmodule
module union_demo (
    input  logic [15:0] in_data,
    output logic [15:0] out_data
);
    typedef union packed {
        logic [15:0] whole;
        struct packed {
            logic [7:0] lo;
            logic [7:0] hi;
        } parts;
    } word_t;
    word_t w;
    always_comb begin
        w.whole  = in_data;
        out_data = {w.parts.lo, w.parts.hi};
    end
endmodule
module bitstream_cast_demo (
    input  logic [31:0] in_word,
    output logic [7:0]  b0,
    output logic [7:0]  b1,
    output logic [7:0]  b2,
    output logic [7:0]  b3
);
    typedef struct packed {
        logic [7:0] byte0;
        logic [7:0] byte1;
        logic [7:0] byte2;
        logic [7:0] byte3;
    } bytes_t;
    bytes_t bs;
    always_comb begin
        bs = bytes_t'(in_word);
        b0 = bs.byte0;
        b1 = bs.byte1;
        b2 = bs.byte2;
        b3 = bs.byte3;
    end
endmodule
