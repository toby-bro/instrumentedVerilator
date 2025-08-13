module m_fork_join_none (
    input  logic        clk,
    input  int          in_data,
    output logic [31:0] out_data
);
    always @(posedge clk) begin : proc_fork_none
        fork : fk_none_label
            begin
                automatic int tmp = in_data + 1;
                out_data <= tmp;
            end
        join_none
    end
endmodule
module m_fork_join_any (
    input  logic       clk,
    input  logic [15:0] a,
    output logic       out_valid
);
    always @(posedge clk) begin : proc_fork_any
        out_valid <= 1'b0;
        fork : fk_any_label
            begin
                automatic int t1 = a * 2;
                if (t1[0]) out_valid <= 1'b1;
            end
            begin
                automatic int t2 = a + 3;
                if (t2[1]) out_valid <= 1'b1;
            end
        join_any
    end
endmodule
module m_nested_task (
    input  logic clk,
    input  int   din,
    output int   dout
);
    task automatic worker(input int d, output int r);
        int temp;
        temp = d + 5;
        fork
            r = temp + 1;
        join
    endtask
    always @(posedge clk) begin : proc_nested_task
        int result;
        worker(din, result);
        dout <= result;
    end
endmodule
module m_class_dynscope (
    input  logic        clk,
    input  logic        start,
    output logic [31:0] result
);
    class Dyn;
        int value;
        function new(int v);
            value = v;
        endfunction
        function void inc();
            value++;
        endfunction
    endclass
    Dyn handle;
    always @(posedge clk) begin : proc_class_dynscope
        if (start) begin
            handle = new(result);
            handle.inc();
            result <= handle.value;
        end
    end
endmodule
module m_event_nb (
    input  logic clk,
    input  logic trigger,
    output logic [3:0] counter
);
    event ev;
    always @(posedge clk) begin : proc_event_trigger
        if (trigger) -> ev;
    end
    always @(ev) begin : proc_event_count
        counter <= counter + 1;
    end
endmodule
module m_var_in_fork (
    input  logic clk,
    input  int   val_in,
    output int   val_out
);
    always @(posedge clk) begin : proc_var_fork
        fork : f_decl
            automatic int local_capture = val_in;
            begin
                automatic int inter = local_capture * 2;
                val_out <= inter;
            end
        join
    end
endmodule
module m_writeback_after_tc (
    input  logic clk,
    input  logic data_in,
    output logic data_out
);
    always @(posedge clk) begin : proc_writeback
        fork
            begin
                data_out <= data_in;
            end
            begin
                @(posedge clk);
                data_out <= ~data_in;
            end
        join_any
    end
endmodule
module m_class_handle_ref (
    input  logic clk,
    input  logic inc,
    output logic [7:0] val
);
    class Holder;
        bit [7:0] data;
        function new(bit [7:0] d);
            data = d;
        endfunction
        function void update(bit do_inc);
            if (do_inc) data++;
        endfunction
    endclass
    Holder h;
    always @(posedge clk) begin : proc_class_handle
        if (h == null) h = new(val);
        h.update(inc);
        val <= h.data;
    end
endmodule
