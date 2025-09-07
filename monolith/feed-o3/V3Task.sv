module inline_task_mod(
    input  logic [7:0] in_a,
    input  logic [7:0] in_b,
    output logic [8:0] out_sum
);
    function automatic int add_default(input int a, input int b = 10);
        add_default = a + b;
    endfunction
    (* no_inline_task *)
    task automatic helper_task(ref int v, const ref int k);
        v = v + k;
    endtask
    always_comb begin
        automatic int temp;
        automatic int k1 = 1;
        automatic int k2 = 2;
        temp = in_a + in_b;
        helper_task(temp, k1);
        helper_task(temp, k2);
        out_sum = add_default(temp);
    end
endmodule
module dpimod(
    input  logic [31:0] in_a,
    input  logic [31:0] in_b,
    output logic [31:0] out_c
);
    import "DPI-C" function int c_add (input int a, input int b);
    export "DPI-C" function sv_mul;
    function int sv_mul (input int a, input int b);
        sv_mul = a * b;
    endfunction
    always_comb begin
        out_c = c_add(in_a, in_b) + sv_mul(in_a, in_b);
    end
endmodule
module classmod(
    input  logic clk,
    input  logic rst_n,
    output logic [7:0] value
);
    class MyClass;
        bit [7:0] v;
        function new(bit [7:0] init = 0);
            v = init;
        endfunction
        function void incr();
            v = v + 1;
        endfunction
        function bit [7:0] get();
            return v;
        endfunction
    endclass
    MyClass obj;
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            obj = new(0);
            value <= 0;
        end else begin
            if (obj == null) obj = new(0);
            obj.incr();
            value <= obj.get();
        end
    end
endmodule
module noinline_mod(
    input  logic clk,
    input  logic rst_n,
    output logic done
);
    int counter;
    (* no_inline_task *)
    task automatic incr(ref int c);
        c = c + 1;
    endtask
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            counter <= 0;
        end else begin
            incr(counter);
        end
    end
    assign done = (counter > 10);
endmodule
module ref_mod(
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] out_a
);
    logic [7:0] var_a;
    logic [7:0] var_b;
    task automatic swap(ref logic [7:0] x, ref logic [7:0] y);
        logic [7:0] tmp;
        tmp = x;
        x = y;
        y = tmp;
    endtask
    always_comb begin
        var_a = a;
        var_b = b;
        swap(var_a, var_b);
        out_a = var_a;
    end
endmodule
module rec_mod(
    input  logic [15:0] n,
    output logic [31:0] fact_out
);
    function automatic int factorial(int i);
        if (i <= 1)
            factorial = 1;
        else
            factorial = i * factorial(i - 1);
    endfunction
    always_comb begin
        fact_out = factorial(n);
    end
endmodule
