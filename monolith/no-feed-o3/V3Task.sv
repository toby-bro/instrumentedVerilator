module inline_task_mod (
    input  logic [7:0] in_a,
    output logic [7:0] out_y
);
    function automatic logic [7:0] incr_f (input logic [7:0] x);
        incr_f = x + 1;
    endfunction
    task automatic do_task (input  logic [7:0] x,
                            output logic [7:0] r);
        r = incr_f(x) + 1;
    endtask
    always_comb begin
        logic [7:0] tmp;
        do_task(in_a, tmp);
        out_y = tmp;
    end
endmodule
module ref_task_mod (
    input  logic        clk,
    input  logic [7:0]  a_in,
    input  logic [7:0]  b_in,
    output logic [7:0]  a_out,
    output logic [7:0]  b_out
);
    task automatic swap (ref int x, ref int y);
        int t;
        t = x;
        x = y;
        y = t;
    endtask
    int ai, bi;
    always_ff @(posedge clk) begin
        ai = a_in;
        bi = b_in;
        swap(ai, bi);
        a_out <= ai[7:0];
        b_out <= bi[7:0];
    end
endmodule
module no_inline_task_mod (
    input  logic [3:0] in_val,
    output logic [3:0] out_val
);
    /*verilator no_inline_task*/
    task automatic mul_by_3 (input  logic [3:0] val,
                             output logic [3:0] res);
        res = val * 3;
    endtask
    always_comb begin
        mul_by_3(in_val, out_val);
    end
endmodule
module dpi_mod (
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] sum,
    output logic [31:0] mult
);
    import "DPI-C" function int c_add_int (input int a, input int b);
    function int sv_mul_int (input int x, input int y);
        sv_mul_int = x * y;
    endfunction
    export "DPI-C" function sv_mul_int;
    always_comb begin
        sum  = c_add_int(a, b);
        mult = sv_mul_int(a, b);
    end
endmodule
module class_constructor_mod (
    input  logic       clk,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    class MyClass;
        int val;
        initial begin
            val = 5;        
        end
        function new (int v = 0);
            val = v;
        endfunction
        function int add (input int x);
            add = val + x;
        endfunction
    endclass
    MyClass obj;
    always_ff @(posedge clk) begin
        if (obj == null) begin
            obj = new(10);
        end
        dout <= obj.add(din);
    end
endmodule
module open_array_mod (
    input  logic clk,
    output logic done
);
    localparam int SIZE = 4;
    int arr[SIZE];
    int res;
    task automatic sum_array (output int s,
                              const ref int a[]);
        int tmp;
        tmp = 0;
        foreach (a[i]) begin
            tmp += a[i];
        end
        s = tmp;
    endtask
    always_ff @(posedge clk) begin
        for (int i = 0; i < SIZE; i++) begin
            arr[i] = i;
        end
        sum_array(res, arr);
    end
    assign done = (res != 0);
endmodule
