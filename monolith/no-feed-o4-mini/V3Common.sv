interface MyIface;
  logic sig;
  modport M(input sig);
endinterface
MyIface intf_inst();
class MyClass;
  int field1;
  logic [7:0] field2;
  function string to_string();
    return { "{", to_string_middle(), "}" };
  endfunction
  function string to_string_middle();
    string out;
    out = { "field1:", field1 };
    out = { out, ",field2:", field2 };
    return out;
  endfunction
endclass
class DerivedClass extends MyClass;
  int z;
  function string to_string_middle();
    string out;
    out = super.to_string_middle();
    out = { out, ",z:", z };
    return out;
  endfunction
endclass
typedef struct {
  int x;
  logic [3:0] y;
} MyStruct;
typedef union {
  bit [7:0] a;
  int b;
} MyUnion;
module basic_mod(input logic [7:0] in, output logic [7:0] out);
  assign out = in;
endmodule
module wide_mod(input logic [127:0] in, output logic out_bit);
  assign out_bit = in[64];
endmodule
module class_mod(input logic [7:0] in, output string out);
  MyClass obj;
  always_comb begin
    obj = new();
    obj.field1 = in;
    out = obj.to_string();
  end
endmodule
module derived_class_mod(input logic [7:0] in, output string out);
  DerivedClass obj;
  always_comb begin
    obj = new();
    obj.field1 = in;
    obj.z = in + 1;
    out = obj.to_string();
  end
endmodule
module struct_mod(input MyStruct in, output int x_out);
  assign x_out = in.x;
endmodule
module union_mod(input MyUnion in, output int b_out);
  assign b_out = in.b;
endmodule
