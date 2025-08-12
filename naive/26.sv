module enum_mux #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in_a,
    input  logic [WIDTH-1:0] in_b,
    input  logic             sel,
    output logic [WIDTH-1:0] out
);
    typedef enum logic [0:0] {SEL_A = 1'b0, SEL_B = 1'b1} sel_t;
    sel_t s;
    always_comb begin
        s = sel ? SEL_B : SEL_A;
        unique case (s)
            SEL_A:  out = in_a;
            SEL_B:  out = in_b;
            default: out = '0;
        endcase
    end
endmodule
module struct_union_example (
    input  logic [15:0] data_in,
    output logic [15:0] data_out
);
    typedef struct packed {
        logic [7:0] lower;
        logic [7:0] upper;
    } byte_split_t;
    typedef union packed {
        byte_split_t bytes;
        logic [15:0] word;
    } word_u;
    word_u convert;
    always_comb begin
        convert.word = data_in;
        data_out     = {convert.bytes.upper, convert.bytes.lower};
    end
endmodule
module parity_array #(
    parameter NUM = 4
)(
    input  logic [NUM-1:0][7:0] data_in,
    output logic [NUM-1:0]      parity_out
);
    genvar i;
    generate
        for (i = 0; i < NUM; i++) begin : parity_gen
            always_comb begin
                parity_out[i] = ^data_in[i];
            end
        end
    endgenerate
endmodule
module class_user (
    input  logic clk,
    input  logic rst_n,
    input  logic req,
    output logic ack
);
    class handshake;
        bit state;
        function void reset();
            state = 0;
        endfunction
        function void request();
            state = 1;
        endfunction
        function bit get_state();
            return state;
        endfunction
    endclass
    handshake hs;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            hs  = new();
            hs.reset();
            ack <= 1'b0;
        end else begin
            if (req) begin
                if (hs == null) hs = new();
                hs.request();
            end
            ack <= hs.get_state();
        end
    end
endmodule
module queue_random #(
    parameter WIDTH = 8
)(
    input  logic                clk,
    input  logic                rst_n,
    input  logic                push,
    input  logic                pop,
    input  logic [WIDTH-1:0]    din,
    output logic [WIDTH-1:0]    dout,
    output logic                empty
);
    logic [WIDTH-1:0] q[$];
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            q.delete();
        end else begin
            if (push)
                q.push_back(din);
            if (pop && (q.size() > 0))
                q.pop_front();
        end
    end
    always_comb begin
        empty = (q.size() == 0);
        dout  = empty ? '0 : q[0];
    end
endmodule
