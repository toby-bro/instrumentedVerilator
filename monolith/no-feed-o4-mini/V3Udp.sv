primitive comb_and2 (y,a,b);
 output y;
 input a,b;
 table
  0 0 : 0;
  0 1 : 1;
  1 0 : 1;
  1 1 : 0;
 endtable
endprimitive
primitive comb_inv (y,a);
 output y;
 input a;
 table
  0 : 1;
  1 : 0;
  x : x;
 endtable
endprimitive
primitive seq_dff (q,d,clk);
 output q; reg q;
 input d,clk;
 initial q = 0;
 table
  0 r : 0 : 0;
  1 r : 1 : 1;
  0 r : 0 : x;
  * 0 : ? : -;
 endtable
endprimitive
primitive seq_latch (q,d,enable);
 output q; reg q;
 input d,enable;
 initial q = 1;
 table
  1 1 : 0 : 1;
  0 1 : 1 : 0;
  0 0 : ? : -;
 endtable
endprimitive
module comb_test(a,b,y);
 input a,b;
 output y;
 wire y;
 assign y = a & b;
endmodule
module seq_test(d,clk,q);
 input d,clk;
 output q;
 wire q;
 seq_dff u_dff(q,d,clk);
endmodule
class MyClass;
endclass
module class_test(clk,out);
 input clk;
 output out;
 logic out,a;
 always_ff @(posedge clk) begin
  MyClass c = new();
  a <= 1'b1;
 end
 assign out = a;
endmodule
