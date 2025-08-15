module func_return #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in_vec,
    output logic [WIDTH-1:0] out_vec
);
    function automatic int compute(input logic [WIDTH-1:0] x);
        int sum;
        sum = 0;
        for (int i = 0; i < WIDTH; i++) begin
            if (x[i]) return i;          
            sum += i;
            if (x == 0) continue;        
        end
        return sum;
    endfunction
    assign out_vec = compute(in_vec);
endmodule
module disable_block (
    input  logic ctrl,
    output logic flag
);
    always_comb begin : main_block
        int acc;
        acc = 0;
        for (int k = 0; k < 8; k++) begin
            acc += k;
            if (ctrl) disable main_block;  
        end
        flag = acc[0];
    end
endmodule
module loop_examples (
    input  logic [3:0] sig,
    output logic [3:0] res
);
    logic [3:0] tmp;
    logic [3:0] task_val;
    task automatic quick_task(input logic [3:0] val, output logic [3:0] ret);
        ret = 0;
        for (int j = 0; j < 4; j++) begin
            if (val[j]) begin
                ret = j;
                return;                    
            end
            ret += j;
        end
    endtask
    always_comb begin
        int i;
        tmp = 0;
        /* verilator unroll_full */
        repeat (4) begin : rpt_blk
            tmp = tmp + 1;
        end
        i = 0;
        /* verilator unroll_full */
        while (i < 4) begin
            if (sig[i]) begin
                i = i + 1;
                continue;                 
            end
            if (sig == 0) break;          
            i = i + 1;
        end
        do begin
            i = i - 1;
        end while (i > 0);
        quick_task(sig, task_val);
        res = task_val ^ tmp ^ i;
    end
endmodule
module foreach_example (
    input  logic [7:0] vec_in,
    output logic       any_set
);
    logic [7:0] local_arr;
    always_comb begin
        local_arr = vec_in;
        any_set   = 1'b0;
        foreach (local_arr[idx]) begin : foreach_loop
            if (local_arr[idx]) begin
                any_set = 1'b1;
                break;                     
            end
            if (!local_arr[idx]) begin
                continue;                  
            end
        end
    end
endmodule
