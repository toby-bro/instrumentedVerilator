module disable_example(
    input  logic        clk,
    input  logic        en,
    output logic [7:0]  q
);
    logic [7:0] d;
    function automatic int dummy_func (input int x);
        dummy_func = x + 1;
    endfunction
    task automatic do_work;
        int i = 0;                
        i  += dummy_func(i);      
        d  <= d + 1;
    endtask
    always @(posedge clk) begin : blk_top
        if (en) begin : active_section
            do_work();            
            q   <= d;
        end
        else begin
            disable active_section; 
        end
    end
endmodule
module timed_stmt_example(
    input  logic        clk,
    input  logic [7:0]  data_in,
    output logic [7:0]  data_out
);
    always begin
        @(posedge clk) data_out <= data_in; 
    end
endmodule
module wait_example(
    input  logic clk,
    input  logic start,
    output logic flag
);
    always @(posedge clk) begin
        flag <= 1'b0;
        wait (start) flag <= 1'b1; 
    end
endmodule
module assertion_example(
    input  logic clk,
    input  logic a,
    output logic b
);
    always @(posedge clk) begin
        b <= a;
        assert (a) else b <= 1'b0; 
    end
endmodule
module event_trigger_example(
    input  logic clk,
    input  logic in_sig,
    output logic out_sig
);
    event my_event;
    always @(posedge clk) begin
        if (in_sig)
            -> my_event;          
    end
    always @(my_event) begin
        out_sig <= ~out_sig;
    end
endmodule
module proc_assign_example(
    input  logic clk,
    input  logic in_sig,
    output logic out_sig
);
    always @(posedge clk) begin
        assign   out_sig = in_sig; 
        deassign out_sig;          
        out_sig  <= in_sig;        
    end
endmodule
module wait_fork_example(
    input  logic clk,
    input  logic go,
    output logic done
);
    task automatic idle_task;
        int x;
        x = 0;
    endtask
    always @(posedge clk) begin
        if (go) begin
            fork
                idle_task();
            join_none
            wait fork;             
            done <= 1'b1;
        end
    end
endmodule
