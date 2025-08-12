module param_module #(parameter int WIDTH = 8) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    localparam int OFFSET = 2;
    assign out = in << OFFSET;
endmodule
module fsm_module (
    input  logic       clk,
    input  logic       rst,
    input  logic [1:0] in,
    output logic       state
);
    typedef enum logic [1:0] {S0, S1, S2, S3} state_t;
    state_t curr, next;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) curr <= S0;
        else    curr <= next;
    end
    always_comb begin
        case (curr)
            S0: next = in[0] ? S1 : S2;
            S1: next = S3;
            S2: next = S0;
            S3: next = S0;
            default: next = S0;
        endcase
    end
    assign state = curr[0];
endmodule
module array_module (
    input  logic        clk,
    input  logic        enable,
    input  logic [7:0]  data_in,
    output logic [7:0]  data_out
);
    logic [7:0] mem [0:3];
    always_ff @(posedge clk) begin
        if (enable) begin
            mem[0] <= data_in;
            mem[1] <= mem[0];
            mem[2] <= mem[1];
            mem[3] <= mem[2];
        end
    end
    assign data_out = mem[3];
endmodule
module generate_module #(
    parameter int N = 4
) (
    input  logic [N-1:0] a,
    output logic [N-1:0] b
);
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : gen_loop
            assign b[i] = ~a[i];
        end
    endgenerate
endmodule
module function_module (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [3:0] sum,
    output logic [3:0] diff
);
    function automatic logic [3:0] add4(input logic [3:0] x, input logic [3:0] y);
        add4 = x + y;
    endfunction
    function automatic logic [3:0] sub4(input logic [3:0] x, input logic [3:0] y);
        sub4 = x - y;
    endfunction
    assign sum  = add4(a, b);
    assign diff = sub4(a, b);
endmodule
module class_module (
    input  logic       clk,
    input  logic       en,
    input  logic [7:0] val_in,
    output logic [7:0] val_out
);
    class calc;
        rand logic [7:0] data;
        function logic [7:0] incr(input logic [7:0] x);
            incr = x + 1;
        endfunction
    endclass
    calc c_inst;
    always_ff @(posedge clk) begin
        if (en) begin
            c_inst = new;
            c_inst.data = val_in;
            val_out <= c_inst.incr(c_inst.data);
        end else begin
            c_inst = new;
            c_inst.data = 0;
            val_out <= c_inst.data;
        end
    end
endmodule
module struct_module (
    input  logic [15:0] in,
    input  logic        sel,
    output logic [7:0]  out
);
    typedef struct packed {
        logic [7:0] hi;
        logic [7:0] lo;
    } pair_t;
    pair_t p;
    always_comb begin
        p = in;
        if (sel) out = p.hi;
        else     out = p.lo;
    end
endmodule
