module return_demo (
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    function automatic logic [7:0] inc (input logic [7:0] v);
        return v + 8'd1;
    endfunction
    function void noop ();
        return;
    endfunction
    always_comb begin
        out_val = inc(in_val);
        noop();
    end
endmodule
module break_continue_demo (
    input  logic [3:0] sel,
    output logic       flag
);
    int i;
    always_comb begin
        flag = 1'b0;
        for (i = 0; i < 10; i++) begin
            if (i == sel) begin
                flag = 1'b1;
                break;
            end
            else begin
                continue;
            end
        end
    end
endmodule
module for_unroll_demo (
    input  logic [7:0] in_a,
    output logic [7:0] out_sum
);
    always_comb begin
        int sum;
        sum = 0;
        for (int i = 0; i < 4; ++i) begin
            sum += in_a + i;
        end
        for (int j = 0; j < 3; j = j + 1) begin
            sum += j;
        end
        out_sum = sum[7:0];
    end
endmodule
module repeat_demo (
    input  logic [3:0] cnt_in,
    output logic [7:0] accum_out
);
    always_comb begin
        int accum;
        accum = 0;
        repeat (cnt_in) begin
            accum += 1;
        end
        accum_out = accum[7:0];
    end
endmodule
module foreach_demo (
    input  logic [7:0] base,
    output logic [7:0] result
);
    logic [7:0] array_2d [0:1][0:3];
    always_comb begin
        int sum;
        sum = 0;
        for (int i = 0; i < 2; i++) begin
            for (int j = 0; j < 4; j++) begin
                array_2d[i][j] = base + j + i;
            end
        end
        foreach (array_2d[i, j]) begin
            sum += array_2d[i][j];
        end
        result = sum[7:0];
    end
endmodule
module while_demo (
    input  logic [3:0] limit,
    output logic [7:0] total
);
    always_comb begin
        int k;
        int t;
        k = 0;
        t = 0;
        while (k < limit) begin
            t += k;
            k++;
        end
        total = t[7:0];
    end
endmodule
module dowhile_demo (
    input  logic [3:0] limit,
    output logic [7:0] total
);
    always_comb begin
        int k;
        int t;
        k = 0;
        t = 0;
        do begin
            t += k;
            k++;
        end while (k < limit);
        total = t[7:0];
    end
endmodule
module forever_demo (
    input  logic [7:0] in_value,
    output logic [7:0] out_value
);
    task automatic do_forever (input int a, output int r);
        int tmp = 0;
        forever begin
            tmp += a;
            if (tmp > 20) begin
                r = tmp;
                break;
            end
        end
    endtask
    always_comb begin
        int res;
        do_forever(in_value, res);
        out_value = res[7:0];
    end
endmodule
