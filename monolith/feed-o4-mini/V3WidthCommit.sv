module width_continuous(input logic signed [7:0] a, input logic [3:0] b, output logic [3:0] y);
  assign y = a[3:0] + b;
endmodule
module width_nonblock(input logic clk, input logic [7:0] d, output logic [7:0] q);
  always_ff @(posedge clk) begin
    q <= d;
  end
endmodule
module cast_module(input logic [3:0] a, input logic signed [3:0] b, output logic [3:0] y);
  assign y = $unsigned(a) + b;
endmodule
module struct_union_module(input logic [3:0] a, output logic [3:0] y);
  typedef struct packed { logic [1:0] x; logic [1:0] z; } mystruct_t;
  typedef union packed { logic [3:0] u; mystruct_t s; } myunion_t;
  mystruct_t st;
  myunion_t un;
  assign st = '{x: a[3:2], z: a[1:0]};
  assign un.s = st;
  assign y = un.u;
endmodule
module enum_typedef_module(input logic [1:0] sel, output logic [7:0] out);
  typedef enum logic [1:0] { IDLE, BUSY, DONE, ERROR } state_t;
  state_t st;
  always_comb begin
    unique case (sel)
      IDLE: st = BUSY;
      BUSY: st = DONE;
      default: st = ERROR;
    endcase
  end
  assign out = {6'd0, st};
endmodule
module param_typedef_module #(parameter int WIDTH = 4) (input logic [WIDTH-1:0] in, output logic [WIDTH-1:0] out);
  typedef logic [WIDTH-1:0] vect_t;
  vect_t v;
  assign v = in;
  assign out = v;
endmodule
module ref_typedef_module(input logic [7:0] i, output logic [7:0] o);
  typedef logic [7:0] byte_t;
  function automatic byte_t foo(ref byte_t a);
    a = a + 1;
    return a;
  endfunction
  byte_t x;
  always_comb begin
    byte_t local_i;
    local_i = i;
    x = foo(local_i);
  end
  assign o = x;
endmodule
module task_module(input logic in, output logic out);
  task automatic tsk(input logic a, output logic b);
    b = a;
  endtask
  logic tmp;
  always_comb begin
    tsk(in, tmp);
  end
  assign out = tmp;
endmodule
module class_module(input logic clk, input logic rst, input logic [3:0] val_in, output logic [3:0] val_out);
  virtual class base;
    virtual function void vfunc(); endfunction
    pure virtual function int pure_f();
  endclass
  class derived extends base;
    function void vfunc(); endfunction
    function int pure_f(); return 1; endfunction
  endclass
  derived drv;
  logic [3:0] tmp;
  always_ff @(posedge clk) begin
    if (rst)
      drv = new;
    if (drv != null) drv.pure_f();
    tmp <= val_in;
  end
  assign val_out = tmp;
endmodule
module constraint_class_module(input logic a, output logic b);
  class cc;
    rand bit [3:0] cvar;
    constraint c1 { cvar > 1; }
    function void method(); endfunction
  endclass
  bit [3:0] x;
  always_comb begin
    automatic cc c = new;
    c.randomize();
    x = c.cvar;
  end
  assign b = a & x[0];
endmodule
module attr_module(input logic a, output logic b);
  (* FOO = "BAR" *) logic x;
  assign x = a;
  assign b = x;
endmodule
package pack1;
  typedef int int_t;
  function automatic int_t add(int_t a, int_t b);
    return a + b;
  endfunction
endpackage
module package_module(input logic in, output logic out);
  import pack1::*;
  logic [3:0] v;
  assign v = add(3, in ? 1 : 0);
  assign out = v[0];
endmodule
interface if1(input logic clk);
  logic sig;
  modport mp (input clk, output sig);
endinterface
module interface_module(input logic clk, output logic sig_out);
  if1 inst(.clk(clk));
  assign sig_out = inst.sig;
endmodule
module dynamic_array_module(input logic [3:0] din, input int idx, output logic [3:0] dout);
  logic [3:0] arr[];
  always_comb begin
    arr = new[4];
    arr[idx] = din;
    dout = arr[idx];
  end
endmodule
