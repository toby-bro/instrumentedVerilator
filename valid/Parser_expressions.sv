//------------------------------------------------------------
class simple;
   int i;
   function new(int v = 0);
      i = v;
   endfunction
endclass
module unary_binary_mixed
      #(parameter WIDTH = 8)
      (input  logic [WIDTH-1:0] ain,
       input  logic [WIDTH-1:0] bin,
       output logic [WIDTH:0]   y);
   always_comb begin
      y = +ain;                        
      y = -y  + ~bin;                  
      y = y | (ain & bin);             
      y = (ain ^ bin) ^~ (ain ~^ bin); 
      y = (ain << 2) + (bin >> 1);     
      y = y && |ain;                   
   end
endmodule
module concat_stream
   (input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [31:0] y);
   always_comb begin
      y = {a, b};          
      y = {4{a}};          
      y = {<<{b}};         
   end
endmodule
module assignment_pattern_struct
   (input  logic [3:0] ain,
    input  logic [3:0] bin,
    output logic [7:0] result);
   typedef struct packed {logic [3:0] a; logic [3:0] b;} s_t;
   s_t temp;
   always_comb begin
      temp   = '{a: ain, b: bin};   
      result = {temp.a, temp.b};
   end
endmodule
module inside_range
   (input  logic [7:0] val,
    output logic       hit);
   always_comb begin
      hit = val inside {8'h00, [8'h10:8'h1F], 8'hFF};
   end
endmodule
module elem_select
   (input  logic [3:0] idx,
    output logic       val);
   logic [15:0] arr = 16'hA5A5;
   always_comb begin
      val = arr[idx + 1];     
   end
endmodule
module new_class_cast
   (input  logic [31:0] in,
    output logic [31:0] out);
   always_comb begin
      simple s = new(int'(in)); 
      out = s.i + 1;            
   end
endmodule
module postfix_incdec
   (input  logic [7:0] a,
    output logic [7:0] out);
   logic [7:0] tmp;
   always_comb begin
      tmp = a;
      tmp++;   
      tmp--;   
      ++tmp;   
      out = tmp;
   end
endmodule
module event_test
   (input  logic clk,
    input  logic rst_n,
    output logic y);
   always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n)
         y <= 1'b0;
      else
         y <= ~y;
   end
endmodule
