module param_example #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    localparam HALF = WIDTH / 2;
    assign out = in + HALF;
endmodule
module gen_example #(parameter WIDTH = 8) (
    input  logic       sel,
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [3:0] y
);
    generate
        if (WIDTH == 8) begin : gen_if
            assign y = sel ? a : b;
        end else begin : gen_else
            assign y = 4'b0000;
        end
    endgenerate
endmodule
module enum_struct_example (
    input  logic        clk,
    input  logic        reset,
    input  logic [1:0]  sel,
    output logic [7:0]  out
);
    typedef enum logic [1:0] { S0 = 2'b00, S1 = 2'b01, S2 = 2'b10 } state_t;
    typedef struct packed { logic [3:0] x; logic [3:0] y; } pair_t;
    state_t    state, next_state;
    pair_t     data;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= S0;
            data  <= '{x:4'd0, y:4'd0};
        end else begin
            state  <= next_state;
            data.x <= data.x + 1;
            data.y <= data.y + 2;
        end
    end
    always_comb begin
        case (sel)
            S0: next_state = S1;
            S1: next_state = S2;
            default: next_state = S0;
        endcase
        out = {data.x, data.y};
    end
endmodule
module union_example (
    input  logic [7:0] in,
    output logic [7:0] out
);
    typedef union packed {
        logic [7:0]           raw;
        struct packed { logic [3:0] hi; logic [3:0] lo; } parts;
    } u_t;
    u_t u;
    always_comb begin
        u.raw      = in;
        u.parts.hi = u.parts.lo + 1;
        out        = u.raw;
    end
endmodule
module class_example (
    input  logic        clk,
    input  logic        rst,
    input  logic [3:0]  a,
    output logic [3:0]  out
);
    class c_example;
        rand logic [3:0] val;
        function void set_val(logic [3:0] v); val = v; endfunction
        function logic [3:0] get_val(); return val; endfunction
    endclass
    c_example c_inst;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            c_inst = new;
            c_inst.set_val(4'd0);
        end else begin
            c_inst.set_val(a);
        end
    end
    always_comb begin
        out = c_inst.get_val();
    end
endmodule
module pipeline_example (
    input  logic        clk,
    input  logic [7:0]  in,
    output logic [7:0]  out
);
    logic [7:0] stage1, stage2;
    always_ff @(posedge clk) begin
        stage1 <= in + 1;
        stage2 <= stage1 + 1;
    end
    assign out = stage2;
endmodule
module functions_example (
    input  logic [3:0]  a,
    input  logic [3:0]  b,
    output logic [4:0]  sum_out,
    output logic [3:0]  diff_out
);
    function automatic logic [4:0] add(input logic [3:0] x, input logic [3:0] y);
        return x + y;
    endfunction
    function automatic logic [3:0] sub(input logic [3:0] x, input logic [3:0] y);
        return x - y;
    endfunction
    assign sum_out  = add(a, b);
    assign diff_out = sub(a, b);
endmodule
