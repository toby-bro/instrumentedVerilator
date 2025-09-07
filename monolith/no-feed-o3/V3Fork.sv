module fork_scope_capture
  (input  logic        clk,
   input  logic [7:0]  in_data,
   output logic [7:0]  out_data);
   always_ff @(posedge clk) begin : parent_block
      int local_val;
      local_val = in_data;
      fork : captured_fork
         begin : child_proc
            automatic int inner = local_val + 1;
            out_data <= inner;
         end
      join_none
   end
endmodule
module fork_join_any_process
  (input  logic       clk,
   input  logic       rst,
   input  logic       in_en,
   output logic       out_done);
   always_ff @(posedge clk) begin
      if (rst) begin
         out_done <= 1'b0;
      end
      else begin
         fork : multiple_paths
            begin : path1
               automatic logic flag1;
               flag1 = in_en;
               @(posedge clk);
               if (flag1) out_done <= 1'b1;
            end
            begin : path2
               automatic int dummy;
               dummy = 0;
               @(posedge clk);
               dummy = dummy + 1;
            end
         join_any
      end
   end
endmodule
module nested_fork_example
  (input  logic        clk,
   input  logic [3:0]  in_value,
   output logic [3:0]  out_value);
   always_ff @(posedge clk) begin
      int val = in_value;
      fork : lvl1
         begin : branch_a
            fork : lvl2
               begin : sub_a1
                  out_value <= val + 4'd5;
               end
            join_none
         end
         begin : branch_b
            out_value <= val - 4'd1;
         end
      join_none
   end
endmodule
module class_handle_fork
  (input  logic       clk,
   input  logic [7:0] in_v,
   output logic [7:0] out_v);
   class myc;
      int d;
      function void set(int x); d = x; endfunction
      function int  get();      return d; endfunction
   endclass
   myc handle;
   always_ff @(posedge clk) begin
      if (handle == null) handle = new;
      handle.set(in_v);
      fork
         begin : class_user
            automatic int temp = handle.get();
            out_v <= temp;
         end
      join_none
   end
endmodule
module write_after_wait
  (input  logic clk,
   input  logic in_signal,
   output logic out_signal);
   always_ff @(posedge clk) begin
      fork
         begin : delayed_write
            automatic logic local_copy = in_signal;
            @(posedge clk);
            out_signal <= local_copy;
         end
      join_none
   end
endmodule
module task_capture_demo
  (input  logic        clk,
   input  logic [15:0] din,
   output logic [15:0] dout);
   task automatic write_task (input int v, output logic [15:0] o);
      o = v;
   endtask
   always_ff @(posedge clk) begin
      fork
         write_task(din, dout);
      join_none
   end
endmodule
