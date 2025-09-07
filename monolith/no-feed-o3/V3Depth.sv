/* ============================================================
   Collection of standalone, executable SystemVerilog modules.
   Each module has at least one input and one output port and
   purposefully exercises a different corner of the Verilator
   frontend, in particular the “depth” and statement handling
   passes present in V3Depth.cpp.
   ============================================================ */
/* ------------------------------------------------------------
   Module 1 : Deeply-nested combinational expression
   ------------------------------------------------------------ */
module depth_expr_mod (
    input  logic [7:0]  a,
    output logic [7:0]  y
);
    /* 100-level nested “+” expression to over-stress depth limiter */
    assign y = (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((a + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a)
                 + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a)
                 + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a)
                 + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a)
                 + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a) + a);
endmodule
/* ------------------------------------------------------------
   Module 2 : Very-wide operator with loop reduction
   ------------------------------------------------------------ */
module wide_op_mod #(
    parameter W = 1024
) (
    input  logic [W-1:0] w_in,
    output logic [31:0]  popcnt
);
    always_comb begin
        integer i;
        popcnt = 0;
        for (i = 0; i < W; i = i + 1) begin
            popcnt = popcnt + w_in[i];
        end
    end
endmodule
/* ------------------------------------------------------------
   Module 3 : Task containing a fork/join (mtask body)
   ------------------------------------------------------------ */
module mtask_body_mod (
    input  logic         clk,
    input  logic  [7:0]  in_data,
    output logic [15:0]  out_data
);
    /* Task that will be executed from an always_ff, shows mtask body */
    task automatic two_way_build (
        input  logic [7:0] di,
        output logic [15:0] do
    );
        automatic logic [15:0] tmp;
        tmp = 0;
        fork
            tmp = {8'h00, di};
            tmp = {di, 8'h00};
        join
        do = tmp;
    endtask
    always_ff @(posedge clk) begin : with_fork
        two_way_build(in_data, out_data);
    end
endmodule
/* ------------------------------------------------------------
   Module 4 : Recursive automatic function
   ------------------------------------------------------------ */
module function_loop_mod (
    input  logic [15:0] n_in,
    output logic [31:0] fib_out
);
    function automatic int unsigned fib (input int unsigned n);
        if (n <= 1) begin
            return n;
        end else begin
            return fib(n-1) + fib(n-2);
        end
    endfunction
    assign fib_out = fib(n_in[7:0]);
endmodule
/* ------------------------------------------------------------
   Module 5 : Class with procedural instantiation
   ------------------------------------------------------------ */
module class_state_mod (
    input  logic [7:0] din,
    output logic [7:0] dout
);
    /* Simple class maintaining internal state */
    class counter;
        bit [7:0] val;
        function new();
            val = 0;
        endfunction
        function bit [7:0] inc (bit [7:0] v);
            val += v;
            return val;
        endfunction
    endclass
    counter c;
    /* Class is instantiated procedurally in a combinational block */
    always_comb begin
        c = new();
        dout = c.inc(din);
    end
endmodule
/* ------------------------------------------------------------
   Module 6 : Unique-case statement
   ------------------------------------------------------------ */
module unique_case_mod (
    input  logic [3:0] sel,
    output logic [7:0] q
);
    always_comb begin
        unique case (sel)
            4'd0:   q = 8'h00;
            4'd1:   q = 8'h11;
            4'd2:   q = 8'h22;
            4'd3:   q = 8'h33;
            4'd4:   q = 8'h44;
            4'd5:   q = 8'h55;
            default q = 8'hFF;
        endcase
    end
endmodule
