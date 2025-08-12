module m_struct_enum #(parameter W = 8) (
    input  logic [W-1:0] a,
    output logic [W-1:0] b
);
    typedef struct packed {
        logic [W-1:0] f1;
        logic          flag;
    } my_struct_t;
    typedef enum logic [1:0] {
        IDLE = 2'b00,
        BUSY = 2'b01,
        DONE = 2'b10
    } state_t;
    my_struct_t s;
    state_t     st;
    always_comb begin
        s.f1   = a;
        s.flag = (a != 0);
        st     = s.flag ? DONE : IDLE;
        b      = (st == DONE) ? s.f1 : '0;
    end
endmodule
module m_union (
    input  logic [7:0] a,
    output logic [7:0] b
);
    union packed {
        logic [3:0] upper;
        logic [3:0] lower;
    } u;
    always_comb begin
        u.upper = a[7:4];
        u.lower = a[3:0];
        b       = {u.upper, u.lower};
    end
endmodule
module m_param_gen #(parameter N = 4) (
    input  logic [N-1:0] in,
    output logic [N-1:0] out
);
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : genblk
            assign out[i] = in[i];
        end
    endgenerate
endmodule
module m_func_task (
    input  logic       clk,
    input  logic       rst_n,
    input  logic [7:0] d,
    output logic [7:0] y
);
    function logic [7:0] incr(input logic [7:0] x);
        incr = x + 1;
    endfunction
    task update(output logic [7:0] q, input logic [7:0] v);
        q = v;
    endtask
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            y <= '0;
        else begin
            logic [7:0] tmp;
            tmp = incr(d);
            update(y, tmp);
        end
    end
endmodule
module m_class_example (
    input  logic       clk,
    input  logic [3:0] in,
    output logic [3:0] out
);
    class my_class;
        rand logic [3:0] data;
        function void compute(input logic [3:0] v);
            data = v + 1;
        endfunction
    endclass
    my_class c;
    always_ff @(posedge clk) begin
        c   = new();
        c.compute(in);
        out = c.data;
    end
endmodule
