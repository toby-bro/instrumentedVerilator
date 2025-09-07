module wait_mod (input  logic clk,
                 input  logic cond,
                 output logic done);
    always_ff @(posedge clk) begin
        wait (cond);          
        done <= 1'b1;
    end
endmodule
module fork_mod (input  logic clk,
                 input  logic a,
                 output logic b);
    always @(posedge clk) fork : myfork
        begin : branch1
            wait (a);
            b <= 1'b0;
        end
        begin : branch2
            b <= a;
        end
    join_none
    always @(posedge clk) begin
        wait fork;
        disable fork;
    end
endmodule
module intra_assign_mod (input  logic clk,
                         input  logic d,
                         output logic q);
    always @(posedge clk) begin
        q = @(negedge clk) d;
    end
endmodule
module named_event_mod (input  logic clk,
                        input  logic trigger,
                        output logic out);
    event ev;
    always @(posedge clk) if (trigger) -> ev;
    always @(ev) out <= 1'b1;
endmodule
class base_c;
    virtual task automatic run(ref int v);
        wait (v == 0);
    endtask
endclass
class child_c extends base_c;
    task automatic run(ref int v);
        super.run(v);
    endtask
endclass
module class_mod (input  logic        clk,
                  input  logic        in,
                  output logic [31:0] out);
    int      val;
    base_c   b;
    child_c  c;
    initial begin
        b = new;
        c = new;
        fork
            b.run(val);
            c.run(val);
        join_none
    end
    always @(posedge clk) if (in) val <= 0;
    assign out = val;
endmodule
