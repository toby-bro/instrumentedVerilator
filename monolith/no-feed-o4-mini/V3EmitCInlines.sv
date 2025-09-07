module AttributeTest(input logic clk, input logic rst, output logic [3:0] out);
   (* DEBUG = "YES" *) logic [3:0] a;
   always_ff @(posedge clk or posedge rst) begin
     if (rst) a <= 0;
     else     a <= a + 1;
   end
   assign out = a;
endmodule
module NewOp(input logic clk, input logic rst, input logic en, output logic [7:0] data_out);
   class MyClass;
     rand bit [7:0] val;
     function void post_randomize(); val = val + 1; endfunction
   endclass
   MyClass c_inst;
   logic [7:0] data_reg;
   always_ff @(posedge clk or posedge rst) begin
     if (rst) data_reg <= 0;
     else if (en) begin
       c_inst = new();
       if (!c_inst.randomize()) ;
       data_reg <= c_inst.val;
     end
   end
   assign data_out = data_reg;
endmodule
module DumpControlTest(input logic clk, input logic rst, output logic sig);
   logic sig_i;
   always_ff @(posedge clk or posedge rst) begin
     if (rst) sig_i <= 0;
     else     sig_i <= ~sig_i;
   end
   assign sig = sig_i;
   initial begin
     $dumpfile("dump.vcd");
     $dumpvars(0, DumpControlTest);
   end
endmodule
module ConditionalTest(input logic [3:0] a, input logic [3:0] b, input logic [3:0] c, output logic [3:0] r);
   assign r = (a & b) ? c : b;
endmodule
module RandCaseBinary(input logic clk, input logic rst, output logic [1:0] state);
   typedef enum logic [1:0] {S0, S1, S2, S3} state_t;
   state_t cur_state;
   always_ff @(posedge clk or posedge rst) begin
     if (rst) cur_state <= S0;
     else begin
       randcase
         1: cur_state = S1;
         1: cur_state = S2;
       endcase
     end
   end
   assign state = cur_state;
endmodule
module RandCaseTernary(input logic clk, input logic rst, output logic [1:0] state);
   typedef enum logic [1:0] {S0, S1, S2, S3} state_t;
   state_t cur;
   always_ff @(posedge clk or posedge rst) begin
     if (rst) cur <= S0;
     else begin
       randcase
         1: cur = S1;
         2: cur = S2;
         3: cur = S3;
       endcase
     end
   end
   assign state = cur;
endmodule
module SimpleModule(input logic [7:0] a, input logic [7:0] b, output logic [7:0] y);
   assign y = a + b;
endmodule
