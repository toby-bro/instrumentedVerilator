package pkg_ex;
  parameter int PKGP = 7;
endpackage
class cls_ex;
  function int cfunc(input int a);
    cfunc = a * 3;
  endfunction
endclass
import "DPI-C" function int dpi_imp(input int a);
export "DPI-C" function dpi_exp;
function int dpi_exp(input int v);
  dpi_exp = v + 5;
endfunction
module mod_const(input logic [1:0] a, output logic b);
  parameter int P1 = 5;
  localparam int LP1 = P1 + 1;
  assign b = a[0] ^ LP1;
endmodule
module mod_scope(input logic a, input logic w, output logic y);
  logic x;
  always_comb begin : SCOPE1
    x = a & w;
  end
  always_comb begin : SCOPE2
    y = x | w;
  end
endmodule
module mod_gen(input logic [1:0] in, output logic [3:0] out);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : GENBLK
      assign out[i] = &in;
    end
  endgenerate
endmodule
module mod_array(input logic [1:0] addr, input logic [3:0] in, output logic out);
  logic [7:0] mem [0:3][0:1];
  assign out = mem[addr][in[1:0]];
endmodule
module mod_param #(parameter int N = 4, parameter type T = logic [3:0]) (input T in, output logic out);
  assign out = in[N-1];
endmodule
module mod_pkg(input logic x, output logic y);
  assign y = x & pkg_ex::PKGP;
endmodule
module mod_cover(input logic clk, input logic [1:0] in, output logic z);
  covergroup CG @(posedge clk);
    coverpoint in {
      bins low = {0};
      bins high = {1,2,3};
    }
  endgroup
endmodule
module mod_func(input logic [3:0] in, output logic [3:0] out);
  function automatic logic [3:0] fnc(input logic [3:0] x);
    fnc = x + 1;
  endfunction
  assign out = fnc(in);
endmodule
module mod_class(input logic [3:0] in, output logic [3:0] out);
  cls_ex cobj;
  always_comb begin
    cobj = new();
    out = cobj.cfunc(in);
  end
endmodule
module mod_dpi_use(input logic [3:0] in, output logic [31:0] out);
  assign out = dpi_imp(in);
endmodule
