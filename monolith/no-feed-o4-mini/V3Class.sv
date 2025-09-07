package pkg1;
typedef struct packed { logic [1:0] a; } S2_t;
class CInPkg;
  static int stat_var;
  static function int get_var();
    return stat_var;
  endfunction
endclass
endpackage
module mod_class_inherit(input logic clk, input logic [3:0] a, output logic [4:0] y);
class Ifc;
  pure virtual function int f(int z);
endclass
class Base;
  function int f(int z);
    return z;
  endfunction
endclass
class Child extends Base implements Ifc;
  function int f(int z);
    return super.f(z) + 1;
  endfunction
endclass
endmodule
module mod_typedef(input logic clk, output logic [7:0] data_out);
typedef struct packed { logic [3:0] a; bit b; } S1_t;
typedef union packed { logic [1:0] c; logic [7:0] d; } U1_t;
S1_t s_reg;
U1_t u_reg;
assign data_out = {s_reg.a, s_reg.b, u_reg.c};
endmodule
module mod_cover(input logic clk, output logic result);
covergroup cg @(posedge clk);
  coverpoint result { bins ok = {1}; }
endgroup
cg cov = new();
endmodule
module mod_vars(input logic clk, input logic [3:0] in_sig, output logic [3:0] out_sig);
logic [3:0] reg1;
bit flag;
function automatic int cfunc_int(int x);
  return x * 2;
endfunction
always_ff @(posedge clk) begin
  reg1 <= in_sig;
  flag <= reg1[0];
end
always_comb begin
  case (reg1)
    4'b0000: out_sig = in_sig;
    default: out_sig = in_sig ^ reg1;
  endcase
end
endmodule
module mod_cfunc(input logic [7:0] val_in, output logic [7:0] val_out);
import "DPI-C" function int c_fun(input int a);
always_comb begin
  val_out = c_fun(val_in);
end
endmodule
module mod_initial(input logic [1:0] a, output logic [1:0] b);
initial begin
  b = a;
end
endmodule
module mod_expr_stmt(input logic [7:0] in1, input logic [7:0] in2, output logic [7:0] out);
genvar i;
generate
  for (i = 0; i < 4; i++) begin : genblk
    logic tmp;
    assign tmp = (in1[i] ? in2[i] : 1'b0);
    assign out[i] = tmp;
  end
endgenerate
endmodule
module mod_task(input logic clk, input logic in_sig, output logic out_sig);
task automatic mytask(input logic a, output logic b);
  logic temp;
  temp = a;
  b = temp;
endtask
always_ff @(posedge clk) begin
  mytask(in_sig, out_sig);
end
endmodule
