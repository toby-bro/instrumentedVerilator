class math_ops;
    function automatic int incr(input int v);
        incr = v + 1;
    endfunction
endclass
module bit_part_sel_mod(
    input  logic [31:0] data,
    input  logic [4:0]  index,
    output logic        bit_out,
    output logic [7:0]  byte_out
);
    always_comb begin
        math_ops m = new();
        bit_out  = data[index];
        byte_out = data[index*8 +: 8];
    end
endmodule
module concat_mod(
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic [7:0] c,
    input  logic [7:0] d,
    output logic [31:0] y
);
    always_comb begin
        math_ops m = new();
        y = {a, {b, {c, d}}};
    end
endmodule
module if_else_mod(
    input  logic [15:0] in1,
    input  logic [15:0] in2,
    input  logic        sel,
    output logic [15:0] y
);
    always_comb begin
        math_ops m = new();
        if (sel) begin
            y = in1;
        end else begin
            y = in2;
        end
    end
endmodule
module ternary_mod(
    input  logic [7:0] in1,
    input  logic [7:0] in2,
    input  logic       sel,
    output logic [7:0] y
);
    always_comb begin
        math_ops m = new();
        y = sel ? in1 : in2;
    end
endmodule
module fork_wait_mod(
    input  logic clk,
    input  logic start,
    output logic finished
);
    event ev1, ev2;
    logic done1 = 1'b0, done2 = 1'b0;
    task automatic parallel_tasks;
        fork
            begin
                wait(start);
                done1 <= 1'b1;
                -> ev1;
            end
            begin
                wait(start);
                done2 <= 1'b1;
                -> ev2;
            end
        join_none
    endtask
    always_ff @(posedge clk) begin
        math_ops m = new();
        if (start) parallel_tasks();
    end
    assign finished = done1 & done2;
endmodule
module func_call_mod(
    input  logic [7:0] a,
    output logic [7:0] y
);
    function automatic [7:0] my_func(input logic [7:0] v);
        my_func = v + 8'd5;
    endfunction
    always_comb begin
        math_ops m = new();
        y = my_func(a);
    end
endmodule
