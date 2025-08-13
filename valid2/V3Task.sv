module ref_task_mod (
    input  logic        clk,
    input  logic [7:0]  in_data,
    output logic [7:0]  out_data
);
    logic [7:0] temp;
    task automatic modify(ref logic [7:0] d);
        d = d + 8'd1;
    endtask
    always_ff @(posedge clk) begin
        temp <= in_data;
        modify(temp);
        out_data <= temp;
    end
endmodule
module inout_task_mod (
    input  logic        clk,
    input  logic [3:0]  in_bus,
    output logic [3:0]  out_bus
);
    logic [3:0] bus_reg;
    task automatic toggle(inout logic [3:0] bus);
        bus = ~bus;
    endtask
    always_ff @(posedge clk) begin
        bus_reg <= in_bus;
        toggle(bus_reg);
        out_bus <= bus_reg;
    end
endmodule
module wide_function_mod (
    input  logic [127:0] a,
    input  logic [127:0] b,
    output logic [127:0] sum
);
    function automatic logic [127:0] wide_add (
        input logic [127:0] x,
        input logic [127:0] y
    );
        wide_add = x + y;
    endfunction
    assign sum = wide_add(a, b);
endmodule
module default_arg_function_mod (
    input  logic [3:0] in_val,
    output logic [3:0] out_val,
    output logic [3:0] out_def
);
    function automatic logic [3:0] inc (
        input logic [3:0] v = 4'd1
    );
        inc = v + 4'd1;
    endfunction
    assign out_val = inc(in_val); 
    assign out_def = inc();       
endmodule
module class_method_mod (
    input  logic       clk,
    output logic [31:0] class_out
);
    class MyClass;
        int val;
        function new (int v);
            val = v;
        endfunction
        function int get();
            return val;
        endfunction
    endclass
    MyClass obj = new(32'd42);
    always_ff @(posedge clk) begin
        class_out <= obj.get();
    end
endmodule
module no_inline_function_mod (
    input  logic        clk,
    input  logic [15:0] din,
    output logic [15:0] dout
);
    logic [15:0] data;
    (* no_inline_task *)
    function automatic logic [15:0] multiply_by2 (input logic [15:0] x);
        multiply_by2 = x << 1;
    endfunction
    always_ff @(posedge clk) begin
        data <= multiply_by2(din);
        dout <= data;
    end
endmodule
module recursive_function_mod (
    input  logic clk,
    input  int   in_n,
    output int   out_result
);
    int res;
    function automatic int fact (int x);
        if (x <= 1)
            fact = 1;
        else
            fact = x * fact(x - 1);
    endfunction
    always_ff @(posedge clk) begin
        res <= fact(in_n);
    end
    assign out_result = res;
endmodule
