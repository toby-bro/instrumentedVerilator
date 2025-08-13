module loop_feature_mod #(parameter W = 8) (
    input  logic  [W-1:0] in_data,
    output logic  [W-1:0] out_data
);
    always_comb begin : main_block
        int j;
        int k;
        out_data = in_data;
        repeat (3) begin : rpt_blk
            int idx_r;
            idx_r = 0;
        end
        k = 0;
        do begin : dw_blk
            k++;
        end while (k < 0);
        j = 0;
        while (j < 4) begin : while_blk
            j++;
            if (j == 2) continue;
            if (j == 3) break;
        end
        for (int m = 0; m < 4; m++) begin : for_blk
            out_data[m % W] = in_data[m % W];
        end
    end
    function automatic logic [W-1:0] modify (input logic [W-1:0] val);
        if (val[0])
            return val;
        else
            return val + 1;
    endfunction
endmodule
module disable_feature_mod (
    input  logic enable_n,
    output logic [3:0] status
);
    always @* begin : proc_block
        status = 4'h0;
        fork : myFork
            begin : blk1
                status = 4'h1;
            end
            begin : blk2
                status = 4'h2;
            end
        join_none
        if (!enable_n) disable myFork;
        begin : namedBlock
            int q;
            q = 0;
        end
        if (!enable_n) disable namedBlock;
    end
endmodule
module foreach_feature_mod (
    input  logic [3:0] sel,
    output logic [7:0] data_out
);
    logic [3:0][7:0] mem;
    always_comb begin
        foreach (mem[i]) begin
            mem[i] = i;
        end
        data_out = mem[sel];
    end
endmodule
module task_feature_mod (
    input  logic [7:0] din,
    output logic [7:0] dout
);
    task automatic process_task (input logic [7:0] t_in, output logic [7:0] t_out);
        t_out = t_in;
        if (t_in == 8'hAA) return;
        repeat (4) begin
            if (t_in[0])
                continue;
            else
                break;
        end
    endtask
    always_comb begin
        process_task(din, dout);
        disable process_task;
    end
endmodule
module pragma_feature_mod (
    input  logic  trig,
    output logic  flag
);
    logic [3:0] a;
    always_comb begin
        flag = 1'b0;
        (* unroll_full *)
        while (a < 0) begin
            a++;
        end
        (* unroll_disable *)
        repeat (2) begin : prg_rpt_blk
            flag = trig;
        end
    end
endmodule
