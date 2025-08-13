module m_fork_join (
    input  logic clk,
    input  logic in_a,
    input  logic in_b,
    output logic out_y
);
    always_ff @(posedge clk) begin : blk_main
        logic br1;
        logic br2;
        fork
            begin : branch1
                br1 = in_a;
            end
            begin : branch2
                br2 = in_b;
            end
        join
        out_y <= br1 ^ br2;
    end
endmodule
module m_fork_join_any (
    input  logic clk,
    input  logic sel,
    output logic out_sel
);
    always_ff @(posedge clk) begin : blk_any
        logic temp;
        fork
            begin : path_one
                if (sel) disable fork;   
            end
            begin : path_two
                temp = ~sel;
            end
        join_any
        out_sel <= temp;
    end
endmodule
module m_fork_join_none (
    input  logic clk,
    input  logic sig,
    output logic o
);
    event e1;
    task automatic trig_event();
        if (sig) -> e1;
    endtask
    task automatic wait_event();
        @(e1);
        o <= 1'b1;
    endtask
    always_ff @(posedge clk) begin : blk_none
        fork
            trig_event();
            wait_event();
        join_none
    end
endmodule
module m_wait_example (
    input  logic clk,
    input  logic trig,
    output logic done
);
    task automatic w_task();
        wait (trig);
        done = 1'b1;
    endtask
    always_ff @(posedge clk) begin : blk_wait
        fork
            w_task();
        join_none
    end
endmodule
