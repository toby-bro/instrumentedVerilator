class Incrementer;
    function automatic logic [7:0] inc(logic [7:0] v);
        inc = v + 8'd1;
    endfunction
endclass
module arithmetic_ops #(
    parameter int WIDTH = 8
)(
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH:0]   sum
);
    always_comb begin
        sum = a + b;
    end
endmodule
module enum_fsm(
    input  logic clk,
    input  logic rst_n,
    input  logic start,
    output logic done
);
    typedef enum logic [1:0] {IDLE, BUSY, FINISH} state_t;
    state_t state, next;
    always_comb begin
        next = state;
        done = 1'b0;
        unique case (state)
            IDLE:   if (start) next = BUSY;
            BUSY:   next = FINISH;
            FINISH: begin
                        done = 1'b1;
                        next = IDLE;
                    end
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next;
    end
endmodule
module struct_union(
    input  logic [31:0] din,
    output logic [31:0] dout
);
    typedef struct packed {
        logic [15:0] low;
        logic [15:0] high;
    } twoword_t;
    union packed {
        twoword_t       s;
        logic [31:0]    word;
    } u;
    always_comb begin
        u.word = din;
        dout   = {u.s.low, u.s.high};
    end
endmodule
module class_demo(
    input  logic [7:0] in,
    output logic [7:0] out
);
    Incrementer inc_obj;
    always_comb begin
        inc_obj = new();
        out = inc_obj.inc(in);
    end
endmodule
module generate_demo #(
    parameter int N = 4
)(
    input  logic [N-1:0] vec_in,
    output logic [N-1:0] vec_out
);
    wire [N-1:0] temp [N-1:0];
    genvar i, j;
    generate
        for (i = 0; i < N; i++) begin : ROW
            for (j = 0; j < N; j++) begin : COL
                assign temp[i][j] = vec_in[i] & vec_in[j];
            end
        end
    endgenerate
    assign vec_out = temp[0];
endmodule
module randomize_demo(
    input  logic        en,
    output logic [15:0] rand_val
);
    logic [15:0] internal;
    initial begin
        void'(std::randomize(internal));
    end
    assign rand_val = en ? internal : 16'h0;
endmodule
