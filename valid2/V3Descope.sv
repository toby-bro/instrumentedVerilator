module leaf (
    input  logic [7:0] in,
    output logic [7:0] out
);
    logic [7:0] inv_cache;
    /*verilator public*/ function automatic logic [7:0] invert (input logic [7:0] x);
        invert = ~x;
    endfunction
    assign inv_cache = invert(in);
    assign out       = inv_cache;
endmodule
module mid (
    input  logic [7:0] in,
    output logic [7:0] out
);
    wire [7:0] w0, w1;
    leaf leaf0 (.in(in),  .out(w0));
    leaf leaf1 (.in(~in), .out(w1));
    /*verilator public*/ function automatic logic [7:0] combine
        (input logic [7:0] a, input logic [7:0] b);
        combine = a ^ b;
    endfunction
    assign out = combine(leaf0.inv_cache, leaf1.inv_cache);
endmodule
module root_mod (
    input  logic [7:0] in,
    output logic [7:0] out
);
    wire [7:0] w0, w1;
    mid m0 (.in(in),  .out(w0));
    mid m1 (.in(~in), .out(w1));
    assign out = m0.leaf0.inv_cache ^ m1.leaf1.inv_cache ^ m0.combine(w0, w1);
endmodule
module dpi_mod (
    input  int a,
    input  int b,
    output int c
);
    import "DPI-C" function int c_add (input int x, input int y);
    /*verilator public*/ function automatic int do_add (input int x, input int y);
        do_add = c_add(x, y);
    endfunction
    assign c = do_add(a, b);
endmodule
module class_mod (
    input  logic        clk,
    input  logic        reset_n,
    output logic [31:0] data_out
);
    class myclass;
        static int count = 0;
        int id;
        function new();
            id = ++count;
        endfunction
        /*verilator public*/ static function int getCount();
            return count;
        endfunction
        function int foo (input int x);
            foo = x + id;
        endfunction
    endclass
    myclass obj;
    always_ff @(posedge clk) begin
        if (!reset_n) begin
            obj = new();
        end
    end
    logic [31:0] temp;
    always_comb begin
        if (obj != null)
            temp = obj.foo(32'hA5A5A5A5);
        else
            temp = 32'h0;
    end
    assign data_out = temp;
endmodule
