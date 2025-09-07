class MyClass;
  bit [3:0] a;
  bit [63:0] wide_b;
  function string to_string();
    return $sformatf("{a:%0d,b:%0d}", a, wide_b);
  endfunction
endclass
class BaseClass;
  bit [7:0] x;
  function string to_string_middle();
    return $sformatf("x:%0d", x);
  endfunction
  function string to_string();
    return { "{", to_string_middle(), "}" };
  endfunction
endclass
class Derived extends BaseClass;
  bit [31:0] y;
  function string to_string_middle();
    return { super.to_string_middle(), $sformatf(",y:%0d", y) };
  endfunction
endclass
class WithStatic;
  static function string static_to_string();
    return "static";
  endfunction
endclass
class ParamClass #(parameter int N = 8);
  bit [N-1:0] data;
  function string to_string();
    return $sformatf("data:%0d", data);
  endfunction
endclass
interface MyIface;
  function string name();
    return "interface_instance";
  endfunction
endinterface
module ClassModule(input logic [3:0] in, output logic [3:0] out);
  always_comb begin
    automatic MyClass mc = new();
    mc.a = in;
    out = mc.a;
  end
endmodule
module DerivedModule(input logic [31:0] in, output logic [31:0] out);
  always_comb begin
    automatic Derived d = new();
    d.y = in;
    out = d.y;
  end
endmodule
module StaticModule(input logic clk, output logic ok);
  always_comb begin
    automatic string s;
    s = WithStatic::static_to_string();
    ok = (s.len() > 0) & clk;
  end
endmodule
module ParamModule(input logic [7:0] in, output logic [7:0] out);
  always_comb begin
    automatic ParamClass #(8) pc = new();
    pc.data = in;
    out = pc.data;
  end
endmodule
module IfaceUser(input logic [7:0] in, output logic [7:0] len);
  MyIface ifc();
  always_comb begin
    automatic string s;
    s = ifc.name();
    len = s.len() + in[0];
  end
endmodule
module StructModule(input logic [15:0] in, output logic [15:0] out);
  typedef struct { logic [7:0] x; logic [15:0] y; } S_t;
  S_t s;
  always_comb begin
    s.x = in[7:0];
    s.y = in;
    out = s.y;
  end
endmodule
module UnionModule(input logic [7:0] in, output logic [7:0] out);
  typedef union { logic [7:0] a; logic [7:0] b; } U_t;
  U_t u;
  always_comb begin
    u.a = in;
    out = u.b;
  end
endmodule
module WideModule(input logic [127:0] in, output logic [127:0] out);
  assign out = in ^ {128{1'b1}};
endmodule
