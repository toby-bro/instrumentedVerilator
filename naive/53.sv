module simple_reg (
    input  logic       clk,
    input  logic       rst,
    input  logic [7:0] d,
    output logic [7:0] q
);
    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            q <= '0;
        else
            q <= d;
    end
endmodule
module param_adder #(
    parameter int WIDTH = 8
) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH-1:0] sum
);
    assign sum = a + b;
endmodule
module gen_shift (
    input  logic       clk,
    input  logic [3:0] in,
    output logic [3:0] out
);
    logic [3:0] regs [0:3];
    genvar i;
    generate
        for (i = 0; i < 3; i = i + 1) begin
            always_ff @(posedge clk)
                regs[i+1] <= regs[i];
        end
    endgenerate
    always_ff @(posedge clk) begin
        regs[0] <= in;
    end
    assign out = regs[3];
endmodule
module struct_union_io (
    input  logic [15:0] data_in,
    output logic [15:0] data_out
);
    typedef struct packed {
        logic [7:0] hi;
        logic [7:0] lo;
    } my_struct_t;
    typedef union packed {
        my_struct_t s;
        logic [15:0] val;
    } my_union_t;
    logic [15:0] tmp;
    always_comb begin
        my_union_t u;
        u.val = data_in;
        if (u.s.hi > u.s.lo)
            tmp = u.s.hi;
        else
            tmp = u.s.lo;
    end
    assign data_out = tmp;
endmodule
module class_inst_block (
    input  logic       clk,
    input  logic [3:0] in,
    output logic [3:0] out
);
    class calc;
        rand bit [3:0] value;
        function void compute(bit [3:0] v);
            value = v + 1;
        endfunction
    endclass
    always_ff @(posedge clk) begin
        static calc c = new;
        c.compute(in);
        out <= c.value;
    end
endmodule
module dyn_queue (
    input  logic       clk,
    input  logic       push,
    input  logic       pop,
    input  logic [7:0] wr_data,
    output logic [7:0] rd_data,
    output logic       empty,
    output logic       full
);
    logic [7:0] queue[$];
    always_ff @(posedge clk) begin
        if (push)
            queue.push_back(wr_data);
        if (pop && queue.size() > 0)
            queue.pop_front();
        rd_data <= (queue.size() > 0) ? queue[0] : '0;
    end
    assign empty = (queue.size() == 0);
    assign full  = (queue.size() >= 16);
endmodule
module localparam_logic (
    input  logic [3:0] in,
    output logic [3:0] out
);
    localparam logic [3:0] MASK = 4'ha;
    assign out = in & MASK;
endmodule
