module fifo_unit #(parameter DEPTH = 4, DATA_WIDTH = 8) (
    input  logic                     clk,
    input  logic                     rst_n,
    input  logic                     push,
    input  logic                     pop,
    input  logic [DATA_WIDTH-1:0]    data_in,
    output logic [DATA_WIDTH-1:0]    data_out,
    output logic                     full,
    output logic                     empty
);
    logic [DATA_WIDTH-1:0] q[$];
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            q.delete();
            data_out <= '0;
        end else begin
            if (push && !full)  q.push_back(data_in);
            if (pop  && !empty) data_out <= q.pop_front();
        end
    end
    assign full  = (q.size() >= DEPTH);
    assign empty = (q.size() == 0);
endmodule
module state_machine_unit (
    input  logic clk,
    input  logic rst_n,
    input  logic in_signal,
    output logic out_signal
);
    typedef enum logic [1:0] {S0, S1, S2} state_t;
    state_t state, next_state;
    always_comb begin
        next_state  = state;
        out_signal  = 1'b0;
        unique case (state)
            S0: if (in_signal) next_state = S1;
            S1: begin
                    out_signal = 1'b1;
                    next_state = S2;
                end
            S2: if (!in_signal) next_state = S0;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) state <= S0;
        else        state <= next_state;
    end
endmodule
module param_vector_unit #(parameter WIDTH = 8, N = 4) (
    input  logic [WIDTH-1:0] vector_in [N],
    output logic [WIDTH-1:0] vector_out[N]
);
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_block
            assign vector_out[i] = ~vector_in[i];
        end
    endgenerate
endmodule
module struct_packer_unit (
    input  logic [7:0] byte_a,
    input  logic [7:0] byte_b,
    output logic [15:0] word_out
);
    typedef struct packed {
        logic [7:0] lsb;
        logic [7:0] msb;
    } word_t;
    word_t tmp_word;
    always_comb begin
        tmp_word.lsb = byte_a;
        tmp_word.msb = byte_b;
        word_out     = tmp_word;
    end
endmodule
module counter_class_unit (
    input  logic           trigger,
    output logic [3:0]     count
);
    class counter_c;
        logic [3:0] val;
        function void increment();
            val = val + 1;
        endfunction
    endclass
    counter_c c;
    always_ff @(posedge trigger) begin
        if (c == null) c = new();
        c.increment();
        count <= c.val;
    end
endmodule
module assertion_unit (
    input  logic        clk,
    input  logic        enable,
    input  logic [7:0]  data_in,
    output logic        ok
);
    always_comb ok = enable & (data_in != 8'h00);
    property p_no_zeros;
        @(posedge clk) disable iff (!enable) data_in != 8'h00;
    endproperty
    assert property (p_no_zeros);
endmodule
