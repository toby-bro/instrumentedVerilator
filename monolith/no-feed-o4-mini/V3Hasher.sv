module basic_dtype(input  logic clk, input  logic rst, input  logic [7:0] a, output logic [15:0] b);
  assign b = {8'hFF, a} ^ {8{a[0]}};
endmodule
module array_dtype(input  logic [3:0] in, output logic [3:0] out);
  logic [7:0] arr1 [0:3];
  always_comb begin
    arr1[0] = in;
    arr1[1] = in << 1;
    arr1[2] = in >> 1;
    arr1[3] = ~in;
    out = arr1[in[1:0]][3:0];
  end
endmodule
module dynamic_array_dtype(input  logic [1:0] idx, output logic [7:0] val);
  logic [7:0] dyn_arr[];
  always_comb begin
    dyn_arr = new[4];
    for (int i = 0; i < 4; i++)
      dyn_arr[i] = i * 3;
    val = dyn_arr[idx];
  end
endmodule
module associative_array_str_dtype(input  logic [3:0] key, output logic [15:0] out);
  logic [15:0] aa[string];
  always_comb begin
    aa["A"] = 10;
    aa["B"] = 20;
    out = aa[$sformatf("%0d", key)];
  end
endmodule
module associative_array_int_dtype(input  int key, output logic [31:0] out);
  int aa[int];
  always_comb begin
    aa[0] = 100;
    aa[1] = 200;
    out = aa[key];
  end
endmodule
module unpack_array(input  logic [1:0] idx, input  logic [7:0] values [0:3], output logic [7:0] val);
  logic [7:0] unpacked[];
  always_comb begin
    unpacked = '{values[0], values[1], values[2], values[3]};
    val = unpacked[idx];
  end
endmodule
module class_instantiation(input  logic [7:0] x, output logic [7:0] y);
  class MyClass;
    int data;
    function new(int d); data = d; endfunction
    function int get(); return data; endfunction
  endclass
  always_comb begin
    MyClass c = new(x);
    y = c.get();
  end
endmodule
module random_class(input  logic [31:0] seed, output logic [7:0] randout);
  class RNG;
    rand bit [7:0] r;
    function new(); endfunction
  endclass
  always_comb begin
    RNG rc = new();
    rc.randomize();
    randout = rc.r;
  end
endmodule
module cast_usage(input  logic signed [7:0] sin, output logic [7:0] y);
  always_comb begin
    logic [3:0] small;
    small = sin;
    y = $signed(sin) + small;
  end
endmodule
interface I_example(input logic clk);
  logic sig;
  modport mp(input sig, output sig);
endinterface
module interface_example(input  logic clk, output logic b);
  I_example intf(.clk(clk));
  always_comb b = intf.sig;
endmodule
module generate_example #(parameter N = 4) (input  logic [N-1:0] in, output logic [N-1:0] out);
  genvar i;
  generate
    for (i = 0; i < N; i++) begin
      assign out[i] = in[i];
    end
  endgenerate
endmodule
module cover_assert(input  logic [7:0] val, output logic ok);
  always_comb begin
    ok = 1;
    assert (val < 255) else ok = 0;
  end
endmodule
module task_function(input  logic a, input  logic b, output logic c, output logic d);
  function logic f1(logic x, logic y);
    return x & y;
  endfunction
  task t1(logic in1, output logic out1);
    out1 = in1;
  endtask
  always_comb begin
    c = f1(a, b);
    t1(c, d);
  end
endmodule
module param_enum(input  logic [1:0] sel, output logic [7:0] out);
  typedef enum logic [1:0] {S0, S1, S2, S3} sel_t;
  always_comb begin
    case (sel)
      S0: out = 8'h00;
      S1: out = 8'h11;
      default: out = 8'hFF;
    endcase
  end
endmodule
module string_test(input  string s, output int len);
  always_comb len = s.len();
endmodule
module typeparam_module #(type T = int) (input  T in, output T out);
  assign out = in;
endmodule
module union_struct(input  logic [7:0] uin, input  logic [7:0] win, output logic [7:0] dout);
  typedef union packed { logic [7:0] u; } u_type;
  typedef struct packed { logic [7:0] w; } s_type;
  u_type ut;
  s_type st;
  always_comb begin
    ut.u = uin;
    st.w = win;
    dout = ut.u ^ st.w;
  end
endmodule
package Pkg;
  parameter int P_CONST = 5;
  typedef struct { int a; } pkg_struct_t;
endpackage
module package_usage(input  logic [3:0] in, output logic [3:0] out);
  import Pkg::*;
  pkg_struct_t ps;
  always_comb begin
    ps.a = P_CONST + in;
    out = ps.a;
  end
endmodule
module recursion_module(input  logic [3:0] n, output logic [15:0] out);
  function logic [15:0] fact(input logic [3:0] x);
    if (x == 0)
      fact = 1;
    else
      fact = x * fact(x - 1);
  endfunction
  always_comb out = fact(n);
endmodule
