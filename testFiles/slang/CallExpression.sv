module call_ordered_named (
    input  logic [7:0] in_data,
    output logic [15:0] out_data
);
    function automatic int adder (input int a, input int b = 2);
        adder = a + b;
    endfunction
    always_comb begin
        int res1;
        int res2;
        int res3;
        res1 = adder(in_data, 4);
        res2 = adder(.b(5), .a(in_data));
        res3 = adder(in_data, .b(6));
        out_data = res1 + res2 + res3;
    end
endmodule
module call_empty_arg (
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    function automatic int foo (input int a = 10, input int b = 20);
        foo = a + b;
    endfunction
    always_comb begin
        int tmp;
        tmp = foo(.b(in_val));
        out_val = tmp[7:0];
    end
endmodule
module call_ref_inout (
    input  logic [7:0] in_sig,
    output logic [7:0] out_sig
);
    function automatic int modify (ref int arg);
        arg = arg + 1;
        modify = arg;
    endfunction
    always_comb begin
        int temp_var = in_sig;
        out_sig = modify(temp_var);
    end
endmodule
module call_task_example (
    input  logic       en,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    task automatic inc (input int a, output int b);
        b = a + 1;
    endtask
    always_comb begin
        if (en) begin
            int tmp;
            inc(din, tmp);
            dout = tmp;
        end
        else begin
            dout = 0;
        end
    end
endmodule
module const_eval_param #(
    parameter int P = 4
) (
    input  logic in_bit,
    output logic out_bit
);
    function automatic int pow2 (input int x);
        pow2 = 1 << x;
    endfunction
    localparam int WIDTH = pow2(P);
    assign out_bit = in_bit;
endmodule
module call_system_function (
    input  logic [7:0] val_in,
    output logic [7:0] unsigned_out
);
    always_comb begin
        unsigned_out = $unsigned(val_in);
    end
endmodule
