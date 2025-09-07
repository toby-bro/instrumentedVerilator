class MyClass;
  bit [7:0] value;
  function new();
    value = 0;
  endfunction
  function bit [7:0] get();
    return value;
  endfunction
  function void set(bit [7:0] v);
    value = v;
  endfunction
endclass
package my_pkg;
  function logic [7:0] pkg_func(input logic [7:0] x);
    return x + 8;
  endfunction
endpackage
module simple_varref(input logic [3:0] in, output logic [3:0] out);
  logic [3:0] a;
  assign a = in;
  assign out = a;
endmodule
module nested_scope(input logic cond, input logic [7:0] data_in, output logic [7:0] data_out);
  generate
    if (1) begin : scopeA
      logic [7:0] dA;
      assign dA = cond ? data_in + 1 : data_in - 1;
    end
  endgenerate
  assign data_out = scopeA.dA;
endmodule
module function_module(input logic [7:0] in, output logic [7:0] out);
  function automatic logic [7:0] f1(input logic [7:0] x);
    logic [7:0] tmp;
    tmp = x << 1;
    return tmp;
  endfunction
  assign out = f1(in);
endmodule
module package_call(input logic [7:0] in, output logic [7:0] out);
  assign out = my_pkg::pkg_func(in);
endmodule
module varscope_mod(input logic clk, input logic rst, input logic [3:0] in, output logic [3:0] out);
  always_ff @(posedge clk) begin : proc_block
    logic [3:0] tmp;
    if (rst)
      tmp = 0;
    else
      tmp = in + 1;
    out <= tmp;
  end
endmodule
module class_usage(input logic [7:0] in, output logic [7:0] out);
  logic [7:0] tmp;
  always_comb begin : compute
    MyClass obj;
    obj = new;
    obj.set(in);
    tmp = obj.get();
    out = tmp;
  end
endmodule
module cmethod_call(input logic [3:0] in, output logic [7:0] out);
  MyClass obj;
  always_comb begin : proc
    obj = new;
    out = obj.get() + obj.value;
  end
endmodule
