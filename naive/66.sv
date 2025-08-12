module param_module #(parameter int WIDTH = 8, parameter int DEPTH = 16) (
    input  logic                   clk,
    input  logic                   rst_n,
    input  logic [WIDTH-1:0]       din,
    output logic [WIDTH-1:0]       dout
);
    class simple_class;
        rand logic [WIDTH-1:0] data;
        function void set(input logic [WIDTH-1:0] x);
            data = x;
        endfunction
    endclass
    simple_class s_obj;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            dout <= '0;
        else begin
            s_obj = new;
            s_obj.set(din);
            dout <= s_obj.data;
        end
    end
endmodule
module comb_module (
    input  logic [3:0] a,
    output logic [3:0] y
);
    always_comb begin
        y = a;
        for (int i = 0; i < 4; i++) begin
            if (a[i])
                y[i] = ~a[i];
        end
    end
endmodule
module latch_module (
    input  logic e,
    input  logic d,
    output logic q
);
    class latch_class;
        logic val;
    endclass
    always_latch begin
        latch_class lc = new;
        if (e) begin
            lc.val = d;
            q      = lc.val;
        end
    end
endmodule
module function_module (
    input  logic [7:0]  in,
    output logic [15:0] out
);
    function automatic logic [15:0] mult2(input logic [7:0] x);
        return x * 2;
    endfunction
    assign out = mult2(in);
endmodule
module struct_union_module (
    input  logic [7:0] in,
    output logic [7:0] out
);
    typedef struct packed { logic [3:0] a; logic [3:0] b; } two_nibbles_t;
    typedef union  packed { logic [7:0] whole; two_nibbles_t parts; } nibble_union_t;
    nibble_union_t u;
    always_comb begin
        u.whole = in;
        out     = {u.parts.b, u.parts.a};
    end
endmodule
module generate_module #(
    parameter int N = 4
) (
    input  logic [N-1:0] in,
    output logic [N-1:0] out
);
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : gen_loop
            assign out[i] = ~in[i];
        end
    endgenerate
endmodule
module queue_module (
    input  logic       clk,
    input  logic       rst,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    logic [7:0] queue_q [$];
    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            queue_q = {};
        else
            queue_q.push_back(din);
    end
    always_comb begin
        if (queue_q.size() > 0)
            dout = queue_q[0];
        else
            dout = '0;
    end
endmodule
