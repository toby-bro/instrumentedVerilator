module wait_proc(input logic clk, input logic req, output logic ack);
   always_ff @(posedge clk) begin
      ack <= 1'b0;
      wait (req);
      ack <= 1'b1;
   end
endmodule
module fork_join_proc(input logic clk, input logic start, output logic done);
   always_ff @(posedge clk) begin
      if (start) begin
         done <= 1'b0;
         fork : ctrlFork
            begin
               done <= 1'b1;
            end
            begin
               wait (done);
            end
         join_none
         wait fork;
         disable fork;
      end
   end
endmodule
module intra_event_assign(input logic clk,
                          input  logic [7:0] in_data,
                          output logic [7:0] out_data);
   always @(posedge clk) begin
      out_data <= @(negedge clk) in_data;
   end
endmodule
module named_event_test(input logic clk, input logic trig, output logic flag);
   event e;
   logic flag_reg;
   assign flag = flag_reg;
   always_ff @(posedge clk) begin
      if (trig) -> e;
   end
   always begin
      @e;
      flag_reg <= 1'b1;
   end
endmodule
class pulse_waiter;
   task automatic wait_pulse(input logic sig);
      @(posedge sig);
   endtask
endclass
module class_method_proc(input logic clk, input logic signal_in, output logic active);
   pulse_waiter pw;
   always_ff @(posedge clk) begin
      if (pw == null) pw = new();
      fork
         begin
            pw.wait_pulse(signal_in);
            active <= 1'b1;
         end
      join_any
   end
endmodule
module constant_wait_m(input logic x, output logic y);
   always @(*) begin
      y = x;
      wait (1);
      y = ~x;
   end
endmodule
