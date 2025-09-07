interface simple_if;
 logic a;
 logic b;
 modport master (output a, input b);
endinterface
interface complex_if #(parameter N=8) ();
 logic [N-1:0] data;
endinterface
module assign_w_mod(input logic in, output logic out, virtual simple_if vif);
 always_comb begin
   vif.a = in;
 end
 assign out = vif.b;
endmodule
module assign_post_mod #(parameter N=8) (input logic clk, output logic out, virtual complex_if #(N) vif);
 always_ff @(posedge clk) begin
   vif.data <= '0;
 end
 assign out = vif.data[0];
endmodule
module if_mod(input logic in, output logic out, virtual simple_if vif);
 always_comb begin
   if (in)
     vif.a = 1'b1;
   else
     vif.a = 1'b0;
 end
 assign out = vif.b;
endmodule
module while_mod(input logic [3:0] count, output logic [3:0] out, virtual complex_if #(4) vif);
 always_comb begin
   out = 0;
   logic [3:0] i;
   i = count;
   while (i != 0) begin
     vif.data[0] = out[0];
     out = out + 1;
     i = i - 1;
   end
 end
endmodule
module jump_mod(input logic in, output logic out, virtual simple_if vif);
 always_comb begin
   block_name: begin
     vif.a = in;
     disable block_name;
   end
   out = vif.b;
 end
endmodule
module for_loop_mod(input logic [3:0] in, output logic [7:0] sum, virtual complex_if #(16) vif);
 always_comb begin
   sum = 0;
   for (int i = 0; i < in; i++) begin
     vif.data = i;
     sum = sum + vif.data;
   end
 end
endmodule
module foreach_mod(input logic [7:0] in_bus [0:3], output logic [7:0] out, virtual simple_if vif);
 always_comb begin
   foreach (in_bus[idx]) begin
     vif.a = in_bus[idx];
     out = idx;
   end
 end
endmodule
module function_mod(input logic in, output logic out, virtual simple_if vif);
 function logic foo(input logic x);
   foo = x & vif.b;
 endfunction
 always_comb begin
   out = foo(in);
   vif.a = out;
 end
endmodule
module class_mod #(parameter WIDTH=8) (input logic clk, input logic reset, output logic [WIDTH-1:0] out, virtual simple_if vif);
 class C;
   int counter;
   function new();
     counter = 0;
   endfunction
   function int next();
     counter = counter + 1;
     return counter;
   endfunction
 endclass
 C myc;
 always_ff @(posedge clk) begin
   if (reset)
     myc = new();
   else begin
     vif.a = 1'b1;
     out <= myc.next();
   end
 end
endmodule
module bad_condition_mod(input logic in, output logic out, virtual simple_if vif);
 always_comb begin
   if (vif.a = in)
     out = vif.b;
 end
endmodule
module bad_loop_mod(input logic in, output logic out, virtual simple_if vif);
 always_comb begin
   logic tmp;
   tmp = in;
   while (tmp && (vif.b = tmp)) begin
     tmp = tmp - 1;
   end
   out = tmp;
 end
endmodule
module case_mod(input logic [1:0] sel, input logic data, output logic out, virtual simple_if vif);
 always_comb begin
   case (sel)
     2'b00: vif.a = data;
     2'b01: begin vif.a = data; end
     default: out = vif.b;
   endcase
 end
endmodule
