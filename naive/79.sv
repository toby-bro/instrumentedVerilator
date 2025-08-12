module param_example #(parameter int WIDTH = 8) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    assign out = in << 1;
endmodule
module array_example (
    input  logic [3:0] a_vals [0:1],
    output logic [3:0] b_vals [0:1]
);
    genvar i;
    generate
        for (i = 0; i < 2; i = i + 1) begin : gen_loop
            assign b_vals[i] = a_vals[i] + i;
        end
    endgenerate
endmodule
module struct_example (
    input  logic [7:0] byte_in,
    output logic [7:0] byte_out
);
    typedef struct packed {
        logic [3:0] hi;
        logic [3:0] lo;
    } nibble_t;
    wire nibble_t n;
    assign n.hi     = byte_in[7:4];
    assign n.lo     = byte_in[3:0];
    assign byte_out = {n.lo, n.hi};
endmodule
module enum_example (
    input  logic [1:0] sel,
    output logic [2:0] code
);
    typedef enum logic [1:0] {
        IDLE = 2'b00,
        BUSY = 2'b01,
        DONE = 2'b10
    } state_t;
    state_t s;
    always_comb begin
        case (sel)
            2'b00: s = IDLE;
            2'b01: s = BUSY;
            default: s = DONE;
        endcase
        code = {1'b1, s};
    end
endmodule
module function_example (
    input  logic [3:0] x,
    output logic [3:0] y
);
    function logic [3:0] f;
        input logic [3:0] v;
        begin
            f = v * v;
        end
    endfunction
    assign y = f(x);
endmodule
module class_example (
    input  logic       clk,
    input  logic       rst,
    output logic [3:0] result
);
    class calc;
        function logic [3:0] add;
            input logic [3:0] a;
            input logic [3:0] b;
            begin
                add = a + b;
            end
        endfunction
    endclass
    calc c;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            result <= '0;
        end else begin
            c = new();
            result <= c.add(result, 4'b0011);
        end
    end
endmodule
module generate_if_example (
    input  logic       en,
    input  logic [7:0] data_in,
    output logic [7:0] data_out
);
    generate
        if (1) begin
            assign data_out = en ? data_in : ~data_in;
        end
    endgenerate
endmodule
module nested_generate_example #(parameter N = 4) (
    input  logic [N-1:0] in,
    output logic [N-1:0] out
);
    logic [N-1:0] temp [N-1:0];
    genvar i, j;
    generate
        for (i = 0; i < N; i = i + 1) begin : row
            for (j = 0; j < N; j = j + 1) begin : col
                assign temp[i][j] = in[(i + j) % N] ^ in[j];
            end
            assign out[i] = ^temp[i];
        end
    endgenerate
endmodule
module bitwise_example (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [3:0] c
);
    assign c = (a & b) | (~a);
endmodule
