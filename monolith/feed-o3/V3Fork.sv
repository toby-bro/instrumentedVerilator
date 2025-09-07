module fork_var_capture(input  logic        clk,
                         input  logic [7:0] din,
                         output logic [7:0] dout);
    always_ff @(posedge clk) begin : proc_capture
        automatic int local_var = 0;
        fork
            begin
                local_var = local_var + din;
                dout      <= local_var;
            end
        join_none
    end
endmodule
module fork_block_declare(input  logic        clk,
                           input  logic [3:0] din,
                           output logic [3:0] dout);
    always_ff @(posedge clk) begin : blk_decl
        fork : F
            automatic int i = din;
            begin
                i = i + 1;
            end
            begin
                dout <= i;
            end
        join_any
    end
endmodule
module nested_fork(input  logic        clk,
                   input  logic [1:0] din,
                   output logic [1:0] dout);
    always_ff @(posedge clk) begin : outer
        fork
            begin : inner_process
                fork
                    begin
                        dout <= din;
                    end
                join_none
            end
        join_none
    end
endmodule
module task_fork(input  logic        clk,
                 input  logic [7:0] din,
                 output logic       result);
    task automatic do_sum(input int x, output int y);
        y = x + 1;
    endtask
    always_ff @(posedge clk) begin : task_block
        int y;
        fork
            begin
                do_sum(din, y);
                result <= y[0];
            end
        join_none
    end
endmodule
class C;
    int value;
    function void set(int v);
        value = v;
    endfunction
endclass
module class_capture(input  logic        clk,
                     input  logic [3:0] din,
                     output logic [3:0] dout);
    C     obj;
    logic init;
    always_ff @(posedge clk) begin : class_proc
        if (!init) begin
            obj  = new;
            init <= 1'b1;
        end
        fork
            begin
                obj.set(din);
            end
            begin
                dout <= obj.value;
            end
        join_any
    end
endmodule
module event_fork(input  logic clk,
                  output logic trig);
    event ev;
    logic done;
    always @(posedge clk) begin : event_proc
        fork
            begin
                -> ev;
                done <= 1'b1;
            end
            begin
                @(ev);
                trig <= done;
            end
        join_any
    end
endmodule
