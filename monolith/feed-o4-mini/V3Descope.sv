module submod(input logic in, output logic out);
  assign out = in;
endmodule
module hier_ref(input logic a, output logic b);
  logic child_out;
  submod u_sub(.in(a), .out(child_out));
  assign b = child_out & a;
endmodule
module nested_scope(input logic in, output logic out);
  logic tmp;
  generate
    begin : BS
      logic inner;
      assign inner = in;
      assign tmp = inner;
    end
  endgenerate
  assign out = tmp;
endmodule
module func_local_ref(input logic in, output logic out);
  logic temp;
  function logic myfunc(input logic x);
    logic y;
    y = x & in;
    return y;
  endfunction
  assign temp = myfunc(in);
  assign out = temp;
endmodule
module class_inst(input logic in, output logic [31:0] out);
  class C;
    rand bit a;
    function void set_a(bit v);
      a = v;
    endfunction
    function bit get_a();
      return a;
    endfunction
    static function int static_fn(int x);
      return x + 1;
    endfunction
  endclass
  C c1;
  logic temp;
  always_comb begin
    c1 = new();
    c1.set_a(in);
    temp = c1.get_a();
    out = C::static_fn(in) + temp;
  end
endmodule
package pkg1;
  typedef enum logic [1:0] {S0, S1} st_t;
  function int pkgfunc(input int x);
    return x + 2;
  endfunction
endpackage
module pkg_ref(input logic [3:0] in, output logic [3:0] out);
  import pkg1::*;
  assign out = pkgfunc(in);
endmodule
module gen_block #(parameter int N = 4)(input logic [N-1:0] in, output logic [N-1:0] out);
  genvar i;
  generate
    for (i = 0; i < N-1; i = i + 1) begin : gen_loop
      assign out[i] = in[i];
    end
    if (N > 2) begin : gen_if
      assign out[N-1] = in[N-1];
    end
  endgenerate
endmodule
interface ifc(input logic clk);
  logic data;
  modport m_out (output data);
endinterface
module if_inst(input logic clk, input logic en, output logic data);
  ifc I(.clk(clk));
  assign I.data = en;
  assign data = I.data;
endmodule
module struct_union_mod(input logic [7:0] in, output logic [7:0] out);
  typedef struct packed { logic [3:0] a; logic [3:0] b; } my_t;
  union packed { my_t s; logic [7:0] u; } uvar;
  assign uvar.s.a = in[3:0];
  assign out = uvar.u;
endmodule
module dyn_arr(input logic clk, input logic en, output logic [7:0] out);
  logic [7:0] arr [0:0];
  always_comb begin
    if (en)
      arr[0] = 8'hAA;
    else
      arr[0] = 8'h00;
  end
  assign out = arr[0];
endmodule
module alias_mod(input logic [3:0] in, output logic [3:0] out);
  typedef logic [3:0] nibble_t;
  nibble_t a;
  assign a = in;
  assign out = a;
endmodule
