module sched_fork_ref (
    input  logic         clk,
    input  logic         rst,
    input  logic  [7:0]  in_data,
    output logic  [7:0]  out_data
);
    always_ff @(posedge clk or posedge rst) begin : proc_main
        automatic logic [7:0] temp;
        automatic int         idx;
        if (rst) begin
            temp     <= '0;
            out_data <= '0;
            idx      <= 0;
        end else begin
            fork : blk_fork_join               
                begin : branch_a
                    temp <= in_data + idx;
                end
                begin : branch_b
                    out_data <= temp;
                    idx      <= idx + 1;
                end
            join
        end
    end
endmodule
module sched_fork_value (
    input  logic        clk,
    input  logic [3:0]  in_sig,
    output logic [3:0]  out_sig
);
    always_ff @(posedge clk) begin : seq_proc
        automatic logic [3:0] local_reg;       
        local_reg <= in_sig;
        fork : blk_fork_none                   
            begin : path1
                out_sig <= local_reg ^ in_sig;
            end
            begin : path2
                /* intentionally left empty */
            end
        join_none
    end
endmodule
module sched_event_control (
    input  logic clk,
    input  logic trig_i,
    output logic flag_o
);
    event ev;
    always_ff @(posedge clk) begin
        if (trig_i) -> ev;                     
    end
    always @(ev) begin                         
        flag_o <= 1'b1;
    end
endmodule
module sched_wait_stmt (
    input  logic clk,
    input  logic cond_i,
    output logic done_o
);
    always_ff @(posedge clk) begin
        done_o <= 1'b0;
        wait (cond_i);                         
        done_o <= 1'b1;
    end
endmodule
module sched_class_usage (
    input  logic clk,
    input  logic in_bit,
    output logic out_bit
);
    class holder_c;
        bit flag;
        function void set(bit v);
            flag = v;
        endfunction
    endclass
    always_ff @(posedge clk) begin
        holder_c h = new();                    
        h.set(in_bit);
        out_bit <= h.flag;
    end
endmodule
