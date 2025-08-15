module fork_vars (
    input  logic        clk,
    input  logic [7:0]  din,
    output logic        dout
);
    always @(posedge clk) begin
        automatic int counter;
        counter <= counter + din;
        fork
            dout <= counter[0];
        join_none
    end
endmodule
module fork_init_decls (
    input  logic        clk,
    input  logic [3:0]  a,
    output logic [3:0]  q
);
    always @(posedge clk) begin
        fork : fork_block
            begin
                automatic int local_a;
                local_a <= a + 1;
                q       <= local_a[3:0];
            end
        join_none
    end
endmodule
module nested_fork_task (
    input  logic        clk,
    input  logic [7:0]  data_in,
    output logic [7:0]  data_out
);
    task automatic process_nested (input logic [7:0] d);
        automatic logic [7:0] tmp;
        tmp <= d + 1;
        fork
            data_out <= tmp;
        join_none
    endtask
    always @(posedge clk) begin
        fork
            process_nested(data_in);
        join_none
    end
endmodule
module class_capture (
    input  logic        clk,
    input  int          in_val,
    output logic [31:0] out_val
);
    class MyObj;
        int val;
        task automatic set_val (int v); val = v; endtask
    endclass
    MyObj obj;
    always @(posedge clk) begin
        if (obj == null) obj <= new;
        fork
            obj.set_val(in_val);
        join_none
        out_val <= obj.val;
    end
endmodule
module event_fork (
    input  logic clk,
    input  logic trig,
    output logic toggled
);
    always @(posedge clk) begin
        event ev;
        fork
            begin
                if (trig) -> ev;
            end
            begin
                @(ev);
                toggled <= ~toggled;
            end
        join_any
    end
endmodule
