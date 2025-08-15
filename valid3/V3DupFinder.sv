module dup_expr(
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] y1,
    output logic [7:0] y2
);
    logic [7:0] t1, t2;
    assign t1 = (a + b) + (a + b);
    assign t2 = (a + b) + (a + b);
    always_comb begin
        y1 = t1 ^ t2;
        y2 = (a & b) | (a & b);
    end
endmodule
module dup_ff(
    input  logic clk,
    input  logic rst_n,
    input  logic d,
    output logic q1,
    output logic q2
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) q1 <= 1'b0;
        else        q1 <= d;
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) q2 <= 1'b0;
        else        q2 <= d;
    end
endmodule
module dup_generate #(
    parameter int WIDTH = 4
)(
    input  logic [WIDTH-1:0] in1,
    input  logic [WIDTH-1:0] in2,
    output logic [WIDTH-1:0] out0,
    output logic [WIDTH-1:0] out1
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : g
            assign out0[i] = in1[i] & in2[i];
            assign out1[i] = in1[i] & in2[i];
        end
    endgenerate
endmodule
module dup_struct(
    input  logic       clk,
    input  logic [3:0] in,
    output logic [3:0] out
);
    typedef struct packed {
        logic [3:0] a;
        logic [3:0] b;
    } pair_t;
    pair_t s1, s2;
    always_ff @(posedge clk) begin
        s1.a <= in;
        s1.b <= in;
        s2   <= s1;
    end
    assign out = s2.a ^ s2.b;
endmodule
module dup_function(
    input  logic [15:0] x,
    input  logic [15:0] y,
    output logic [15:0] z1,
    output logic [15:0] z2
);
    function automatic logic [15:0] adddup(input logic [15:0] p, input logic [15:0] q);
        adddup = (p + q) + (p + q);
    endfunction
    assign z1 = adddup(x, y);
    assign z2 = adddup(x, y);
endmodule
module dup_class(
    input  logic [3:0] in_data,
    output logic [3:0] out_data
);
    class DataHolder;
        logic [3:0] data;
        function new(logic [3:0] d);
            data = d;
        endfunction
    endclass
    DataHolder h1;
    DataHolder h2;
    always_comb begin
        h1 = new(in_data);
        h2 = new(in_data);
        out_data = h1.data ^ h2.data;
    end
endmodule
module dup_union(
    input  logic [7:0] din,
    output logic [7:0] dout
);
    typedef union packed {
        logic [7:0] u8;
        struct packed {logic [3:0] lo; logic [3:0] hi;} nybble;
    } u_t;
    u_t u1, u2;
    always_comb begin
        u1.u8 = din;
        u2.u8 = din;
        dout  = u1.u8 | u2.u8;
    end
endmodule
module dup_enum(
    input  logic [1:0] sel,
    output logic       match
);
    typedef enum logic [1:0] { A = 2'b00, B = 2'b01, C = 2'b10, D = 2'b11 } e_t;
    e_t e1, e2;
    always_comb begin
        e1 = e_t'(sel);
        e2 = e_t'(sel);
        match = (e1 == e2);
    end
endmodule
