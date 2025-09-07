typedef struct { logic [3:0] x; logic [3:0] y; } SType;
package MyPkg;
  class PkgClass;
    function int inc(int v);
      return v + 1;
    endfunction
  endclass
endpackage
interface BusIf(input logic clk);
  logic [7:0] data;
endinterface
module UnionMod(input logic [15:0] in, output logic [7:0] out);
  union { logic [7:0] a; logic [15:0] b; } u;
  assign u.b = in;
  assign out = u.a;
endmodule
module StructMod(input logic [7:0] a, output logic [15:0] b);
  SType s;
  assign s.x = a[3:0];
  assign s.y = a[7:4];
  assign b = {s.x, s.y};
endmodule
module Child(input logic in, output logic out);
  assign out = in;
endmodule
module Parent(input logic in, output logic out);
  Child child_inst(.in(in), .out(out));
endmodule
module CFuncMod(input logic [31:0] a, output logic [31:0] b);
  import "DPI-C" function int ext_func(input int x);
  function int svfunc(input int y);
    return ext_func(y);
  endfunction
  always_comb begin
    b = svfunc(a);
  end
endmodule
module VirtMod(input logic clk, input logic [7:0] in, output logic [7:0] out);
  BusIf vif(clk);
  always_comb begin
    out = vif.data ^ in;
  end
endmodule
module ClassMod(input logic [7:0] i, output logic [7:0] o);
  class LocalClass;
    function logic [7:0] transform(logic [7:0] v);
      return ~v;
    endfunction
  endclass
  LocalClass obj;
  always_comb begin
    obj = new();
    o = obj.transform(i);
  end
endmodule
module PkgClassMod(input logic [7:0] i, output logic [31:0] o);
  MyPkg::PkgClass pc;
  always_comb begin
    pc = new();
    o = pc.inc(i);
  end
endmodule
