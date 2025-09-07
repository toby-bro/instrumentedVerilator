module sv_instr_select_ops #(
    parameter WIDTH = 32
) (
    input  logic [WIDTH-1:0] in0,
    input  logic [WIDTH-1:0] in1,
    input  logic [WIDTH-1:0] in2,
    input  logic [WIDTH-1:0] in3,
    input  logic [3:0]       sel_index,
    output logic [WIDTH-1:0] word_out,
    output logic             bit_out,
    output logic [WIDTH*4-1:0] concat_out
);
    logic [WIDTH-1:0] vec [0:3];
    always_comb begin
        vec[0] = in0;
        vec[1] = in1;
        vec[2] = in2;
        vec[3] = in3;
    end
    assign word_out = vec[sel_index[1:0]];
    assign bit_out  = word_out[sel_index];
    assign concat_out = {vec[0], vec[1], vec[2], vec[3]};
endmodule
module sv_instr_conditional (
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic       sel,
    output logic [7:0] y,
    output logic [7:0] z
);
    always_comb begin
        (* branch_predict = "likely" *)
        if (a > b) begin
            y = a + b;
        end else begin
            y = a - b;
        end
    end
    assign z = sel ? a : b;
endmodule
module sv_instr_fork_task (
    input  logic        clk,
    input  logic        start,
    input  logic [31:0] in_a,
    input  logic [31:0] in_b,
    output logic [31:0] out_r
);
    function automatic logic [31:0] myfunc (input logic [31:0] x);
        myfunc = x + 32'd1;
    endfunction
    task automatic mytask (
        input  logic [31:0] x,
        input  logic [31:0] y,
        output logic [31:0] r
    );
        r = x ^ y;
    endtask
    always_ff @(posedge clk) begin
        if (start) begin
            fork
                begin
                    logic [31:0] tmp;
                    mytask(in_a, in_b, tmp);   
                    out_r <= tmp;
                end
                begin
                    out_r <= myfunc(in_a);      
                end
            join
        end
    end
endmodule
module sv_instr_class (
    input  logic        clk,
    input  logic [31:0] din,
    output logic [31:0] dout
);
    class holder;
        int value;
        function new (int v);
            value = v;
        endfunction
        function int get ();
            return value;
        endfunction
    endclass
    always_ff @(posedge clk) begin
        holder h = new(din);
        dout     <= h.get();
    end
endmodule
