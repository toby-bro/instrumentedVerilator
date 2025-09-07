module fork_basic(
    input  logic        clk,
    input  logic        rst_n,
    input  logic [7:0]  in_data,
    output logic [7:0]  out_data
);
    always_ff @(posedge clk or negedge rst_n) begin : PROC_MAIN
        if (!rst_n) begin
            out_data <= 8'd0;
        end else begin
            fork : BASIC_FORK
                begin : PATH_A
                    automatic logic [7:0] tmp;
                    tmp = in_data;
                    out_data <= tmp;
                end
                begin : PATH_B
                    automatic logic [7:0] tmp2;
                    tmp2 = in_data + 1;
                    out_data <= tmp2;
                end
            join
        end
    end
endmodule
module fork_nested(
    input  logic clk,
    input  logic rst,
    input  logic in_sig,
    output logic out_sig
);
    always_ff @(posedge clk) begin : NESTED_PROC
        if (rst) begin
            out_sig <= 1'b0;
        end else begin
            fork : OUTER_FORK
                begin : BRANCH1
                    out_sig <= in_sig;
                    fork : INNER_FORK
                        begin : INNER1
                            out_sig <= ~in_sig;
                        end
                        begin : INNER2
                            out_sig <= in_sig & ~out_sig;
                        end
                    join_any
                end
                begin : BRANCH2
                    out_sig <= in_sig ^ out_sig;
                end
            join
        end
    end
endmodule
module fork_join_none(
    input  logic clk,
    input  logic start,
    output logic done
);
    logic started;
    always_ff @(posedge clk) begin : START_PROC
        if (!started && start) begin
            started <= 1'b1;
            fork : PAR_FORK
                begin : CHILD_A
                    done <= 1'b0;
                end
                begin : CHILD_B
                    done <= 1'b1;
                end
            join_none
        end
    end
    always_ff @(posedge clk) begin : CONTROL_PROC
        if (done) disable PAR_FORK;
    end
endmodule
module event_sched(
    input  logic clk,
    input  logic trigger,
    output logic flag
);
    event evTrig;
    always_ff @(posedge clk) begin : TRIGGER_PROC
        if (trigger) -> evTrig;
    end
    always @(evTrig) begin : RESP_PROC
        flag = 1'b1;
    end
endmodule
module task_fork(
    input  logic clk,
    input  logic src,
    output logic dst
);
    task automatic process_task(input logic in, output logic out);
        fork
            begin : T1
                out = in;
            end
        join
    endtask
    always_ff @(posedge clk) begin : CALL_PROC
        process_task(src, dst);
    end
endmodule
module class_inst(
    input  logic clk,
    input  logic a,
    output logic b
);
    class dummy;
        bit data;
    endclass
    always_ff @(posedge clk) begin : CLASS_PROC
        dummy d = new();
        d.data = a;
        b      <= d.data;
    end
endmodule
module wait_proc(
    input  logic clk,
    input  logic en,
    output logic outp
);
    always_ff @(posedge clk) begin : WAIT_PROC
        fork : WAIT_FORK
            begin : WAIT_BRANCH
                wait (en);
                outp <= 1'b1;
            end
        join
    end
endmodule
