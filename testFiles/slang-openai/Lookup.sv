package def_pkg;
  typedef enum logic [1:0] {ST_IDLE, ST_BUSY, ST_ERR} state_e;
  parameter int PKG_P = 4;
  class base #(type T = int, int N = 8);
    static int static_var;
    protected T prot_var;
            int loc_var;
    function new();
      prot_var = '0;
    endfunction
    function int getN();
      return N;
    endfunction
  endclass
  class derived extends base#(byte, 16);
    function new();
      super.new();
      this.prot_var = 8'hFF;
    endfunction
    function int sum (int a, int b);
      return a + b;
    endfunction
  endclass
  function int add_one (input int x);
    return x + 1;
  endfunction
endpackage
interface bus_if (input logic clk);
  logic [7:0] data;
  modport mp (input clk, output data);
endinterface
typedef enum int {ALPHA = 1, BETA = 2} global_e;
typedef struct packed {logic [7:0] byte_f;} foo_s;
module pkg_demo (input  logic i,
                 output logic o);
  import def_pkg::*;
  state_e st;
  derived d_handle;
  always_comb begin
    d_handle = new();
    st       = ST_IDLE;
    o        = i;
  end
endmodule
module gen_array #(parameter int N = 4)
                  (input  logic din,
                   output logic dout);
  logic [N-1:0] sig;
  genvar idx;
  for (idx = 0; idx < N; idx++) begin : g_blk
    assign sig[idx] = din;
  end
  assign dout = sig[2] & &sig;
endmodule
module class_access (input  logic clk,
                     output logic [31:0] val);
  class Base;
    int x;
    function new (int v); x = v; endfunction
    virtual function int get(); return x; endfunction
  endclass
  class Child extends Base;
    function new (int v); super.new(v); endfunction
    function int getPlusOne(); return super.get() + 1; endfunction
  endclass
  Child obj;
  always_comb begin
    obj = new(10);
    val = obj.getPlusOne();
  end
endmodule
module generic_class_use (input  logic a,
                          output logic b);
  import def_pkg::*;
  base#(int, 12) bc;
  always_comb begin
    bc = new();
    b  = a;
  end
endmodule
module unit_scope_ref (input  logic a,
                       output logic o);
  global_e state;
  foo_s    myfoo;
  always_comb begin
    state        = $unit::ALPHA;
    myfoo.byte_f = 8'hAA;
    o            = a & state[0];
  end
endmodule
module enum_access (input  logic in,
                    output logic out);
  typedef enum {RED, GREEN, BLUE} color_e;
  color_e color;
  always_comb begin
    color = GREEN;
    out   = in;
  end
endmodule
module temp_var_demo (input  logic din,
                      output logic dout);
  always_comb begin : proc
    automatic int temp;
    temp = din;
    dout = temp;
  end
endmodule
module forward_typedef_demo (input  logic din,
                             output logic dout);
  typedef struct packed {logic a;} foo_t;
  foo_t bar;
  always_comb begin
    bar.a = din;
    dout  = bar.a;
  end
endmodule
