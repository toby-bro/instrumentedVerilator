interface bus_if #(parameter WIDTH = 8);
    logic [WIDTH-1:0] data;
    logic             valid;
    modport m (input  data, input  valid);
    modport s (output data, output valid);
endinterface
module bitwise_and #(parameter WIDTH = 4)(
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH-1:0] y
);
    assign y = a & b;
endmodule
module state_machine(
    input  logic clk,
    input  logic rst_n,
    input  logic in_sig,
    output logic out_sig
);
    typedef enum logic [1:0] { S0, S1, S2 } state_t;
    state_t state, next;
    always_comb begin
        next    = state;
        out_sig = 1'b0;
        unique case (state)
            S0: if (in_sig) next = S1;
            S1: begin
                    out_sig = 1'b1;
                    next    = S2;
                end
            S2: if (!in_sig) next = S0;
            default: next = S0;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= S0;
        else
            state <= next;
    end
endmodule
module parametrized_counter #(
    parameter WIDTH = 16,
    parameter STEP  = 1
)(
    input  logic             clk,
    input  logic             rst_n,
    output logic [WIDTH-1:0] count
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= '0;
        else
            count <= count + STEP;
    end
endmodule
module struct_union_example(
    input  logic [31:0] data_in,
    output logic [7:0]  byte0_out
);
    typedef struct packed {
        logic [7:0] byte0;
        logic [7:0] byte1;
        logic [7:0] byte2;
        logic [7:0] byte3;
    } word_t;
    typedef union packed {
        word_t       word;
        logic [31:0] raw;
    } union_t;
    union_t u;
    always_comb begin
        u.raw     = data_in;
        byte0_out = u.word.byte0;
    end
endmodule
module class_compute(
    input  logic [15:0] a,
    input  logic [15:0] b,
    output logic [15:0] sum
);
    class adder_c;
        function automatic logic [15:0] add(logic [15:0] x, logic [15:0] y);
            return x + y;
        endfunction
    endclass
    always_comb begin
        adder_c ad;
        ad = new();
        sum = ad.add(a, b);
    end
endmodule
module generate_block #(parameter WIDTH = 8)(
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] reversed
);
    always_comb begin
        for (int i = 0; i < WIDTH; i++) begin
            reversed[i] = in[WIDTH-1-i];
        end
    end
endmodule
