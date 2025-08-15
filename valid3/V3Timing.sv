`timescale 1ns/1ps
module wait_cond_mod (
    input  logic clk,
    input  logic cond_in,
    output logic state_out
);
    always @(posedge clk) begin
        wait (cond_in);
        state_out <= ~state_out;
    end
endmodule
module variable_wait_mod (
    input  logic clk,
    input  logic trigger_in,
    output logic done
);
    always @(posedge clk) begin
        wait (trigger_in);
        done <= 1'b1;
    end
endmodule
module fork_waitfork_mod (
    input  logic clk,
    input  logic start,
    output logic finished
);
    logic internal_done;
    always @(posedge clk) begin
        if (start) begin
            internal_done <= 1'b0;
            fork
                begin : branch_a
                    internal_done <= 1'b1;
                end
                begin : branch_b
                    wait (internal_done);
                end
            join_any
            wait fork;
            finished <= internal_done;
        end
    end
endmodule
module fork_disable_mod (
    input  logic clk,
    input  logic go,
    output logic flag
);
    always @(posedge clk) begin
        if (go) begin
            fork : async_threads
                begin : t1
                    wait (!go);
                end
                begin : t2
                    flag <= 1'b1;
                end
            join_none
            wait (go);
            disable fork;
        end
    end
endmodule
module named_event_mod (
    input  logic clk,
    output logic toggle
);
    event e_trigger;
    always @(posedge clk) begin
        -> e_trigger;
    end
    always @(e_trigger) begin
        toggle <= ~toggle;
    end
endmodule
class wait_class;
    task automatic wait_for (ref logic sig);
        wait (sig);
    endtask
endclass
module class_timing_mod (
    input  logic clk,
    input  logic trig,
    output logic ack
);
    wait_class w_inst;
    initial begin
        w_inst = new();
    end
    always @(posedge clk) begin
        fork
            w_inst.wait_for(trig);
        join_none
        wait fork;
        ack <= 1'b1;
    end
endmodule
module nested_begin_mod (
    input  logic clk,
    input  logic a,
    output logic y
);
    always @(posedge clk) begin
        begin
            if (a) begin
                y <= ~y;
            end
        end
    end
endmodule
