module var_scope_mod(input logic clk, input logic [7:0] a, output logic [7:0] b);
   parameter int P = 4;
   localparam logic [3:0] LP = 4'd7;
   logic signed [15:0] var_s;
   genvar i;
   generate
      for (i = 0; i < 1; i++) begin : regs
         logic [1:0] lb;
         assign lb = 2'b01;
      end
   endgenerate
   always_comb begin
      var_s = a;
      b = a + var_s[7:0] + regs[0].lb;
   end
endmodule
module fn_task_mod(input logic [3:0] in, output logic [3:0] out);
   function automatic logic [3:0] f1(logic [3:0] x);
      return x + 1;
   endfunction
   task automatic t1(input logic [3:0] x, output logic [3:0] y);
      y = x + 2;
   endtask
   always_comb begin
      logic [3:0] tmp;
      out = f1(in);
      t1(in, tmp);
      out = out + tmp;
   end
endmodule
module dpi_mod(input int a, output int b);
   import "DPI-C" function int cfunc(input int x);
   always_comb begin
      b = cfunc(a);
   end
endmodule
module cover_mod(input logic [1:0] s, output logic z);
   covergroup cg @(posedge s[0]);
      cp1: coverpoint s[1];
      cp2: coverpoint s[0];
      cross cp1, cp2;
   endgroup
   cg my_cg = new();
   always_comb begin
      z = s[0] & s[1];
   end
endmodule
module struct_union_mod(input logic [7:0] d, output logic [7:0] e);
   typedef struct packed { logic [3:0] f; struct packed { logic g; } inner; } mystruct_t;
   typedef union packed { logic [7:0] u1; logic [7:0] u2; } myunion_t;
   mystruct_t ms;
   myunion_t mu;
   always_comb begin
      ms.f = d[3:0];
      ms.inner.g = d[4];
      mu.u1 = d;
      e = mu.u2;
   end
endmodule
module class_mod(input logic [7:0] in, output logic [7:0] out);
   class Base;
      int x;
      function new; x = 1; endfunction
      virtual function int get(); return x; endfunction
   endclass
   class Derived extends Base;
      int y;
      function new; super.new(); y = 2; endfunction
      function int sum(); return x + y; endfunction
   endclass
   Derived d = new;
   always_comb begin
      out = d.sum() + in;
   end
endmodule
