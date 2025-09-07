module m_remap(
    input  logic clk,
    input  logic a,
    input  logic b,
    output logic y
);
    event ev_a, ev_b;
    logic temp;
    always_ff @(posedge clk) begin
        temp <= a & b;
        if (a) -> ev_a;
        if (b) -> ev_b;
    end
    always @(ev_a or ev_b) begin : event_handler
        y <= temp;
    end
endmodule
module m_timing(
    input  logic clk,
    input  logic start,
    output logic done
);
    event start_ev;
    logic done_r;
    always_ff @(posedge clk) begin
        if (start) -> start_ev;
    end
    task automatic resume_task();
        forever begin
            @(start_ev);
            done_r = 1'b1;
        end
    endtask
    always_ff @(posedge clk) begin : resume_process
        fork : resume_fork
            resume_task();
        join_none
    end
    assign done = done_r;
endmodule
module m_fork_transform(
    input  logic clk,
    input  logic in1,
    input  logic in2,
    output logic out1
);
    logic r1, r2;
    always_ff @(posedge clk) begin : main_proc
        fork : parallel_block
            begin : path_a
                if (in1) r1 <= ~r1;
            end
            begin : path_b
                if (in2) r2 <= ~r2;
            end
        join_any
    end
    assign out1 = r1 ^ r2;
endmodule
module m_dynamic(
    input  logic clk,
    input  logic trig,
    output logic flag
);
    event ev_dyn;
    logic state;
    always_ff @(posedge clk) begin
        if (trig) -> ev_dyn;
    end
    always @(ev_dyn) begin
        state = ~state;
    end
    assign flag = state;
endmodule
module m_wait_disable(
    input  logic clk,
    input  logic go,
    output logic status
);
    event ev_go;
    logic done;
    always_ff @(posedge clk) begin
        if (go) -> ev_go;
    end
    task automatic worker();
        @(ev_go);
        done = 1'b1;
    endtask
    always_ff @(posedge clk) begin : controller
        fork
            worker();
            begin : sync_block
                wait (done);
                disable fork;
            end
        join
        status <= done;
    end
endmodule
