module repeat_loop (
    input  logic [3:0] in_count,
    output logic [7:0] out_total
);
    always_comb begin : REP_BLOCK
        int acc = 0;
        repeat (in_count) begin
            acc += 1;
        end
        out_total = acc;
    end
endmodule
module while_break_continue (
    input  logic [3:0] in_val,
    output logic [7:0] out_sum
);
    always_comb begin : WHILE_BLOCK
        int i   = 0;
        int sum = 0;
        while (i < in_val) begin
            i++;
            if (i == 2) continue;
            if (i == 5) break;
            sum += i;
        end
        out_sum = sum;
    end
endmodule
module do_while_loop (
    input  logic [3:0] in_val,
    output logic [7:0] out_sum
);
    always_comb begin : DO_BLOCK
        int i   = 0;
        int val = 0;
        do begin
            val += i;
            i++;
        end while (i < in_val);
        out_sum = val;
    end
endmodule
module foreach_example (
    input  logic [3:0] limiter,
    output logic [7:0] out_sum
);
    logic [7:0] arr [0:15];
    always_comb begin : FOREACH_BLOCK
        int sum = 0;
        foreach (arr[idx]) begin
            arr[idx] = idx;
            if (idx >= limiter) break;
            sum += arr[idx];
        end
        out_sum = sum;
    end
endmodule
module named_begin_disable (
    input  logic [3:0] in_data,
    output logic [7:0] out_data
);
    always_comb begin : OUTER
        int result = 0;
        begin : INNER
            if (in_data == 0) disable OUTER;
            result = in_data + 1;
        end
        out_data = result;
    end
endmodule
module fork_disable_example (
    input  logic        clk,
    input  logic [3:0]  in_data,
    output logic [7:0]  out_data
);
    task automatic do_parallel (input int n, output int res);
        res = 0;
        fork
            begin
                res = n + 1;
            end
            begin
                res = n + 2;
            end
        join_any
        disable fork;
    endtask
    always_ff @(posedge clk) begin : MAIN
        int temp;
        do_parallel(in_data, temp);
        out_data <= temp;
    end
endmodule
module function_return_example (
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    function automatic int inc_if_not_zero (input int x);
        if (x == 0) return 0;
        return x + 1;
    endfunction
    always_comb begin
        out_val = inc_if_not_zero(in_val);
    end
endmodule
module unroll_example (
    input  logic [7:0] in_bus,
    output logic [7:0] out_acc
);
    always_comb begin : UNROLL_BLOCK
        int acc = 0;
        /* verilator unroll_full */
        for (int i = 0; i < 8; i++) begin
            acc += in_bus[i];
        end
        out_acc = acc;
    end
endmodule
