package my_pkg;
  int pkg_state = 0;
  function automatic int pkg_increment(input int val);
    pkg_state = pkg_state + val;
    return pkg_state;
  endfunction
endpackage
interface simple_if (input logic clk);
  logic a;
  logic b;
  modport m (input a, output b);
endinterface
module dut_alias (
    input  logic i_sig,
    output logic o_sig
);
  wire w1;
  wire w2;
  alias w1 = w2;
  assign w1 = i_sig;
  assign o_sig = w2;
endmodule
module dut_cover (
    input logic clk,
    input logic i_sig,
    output logic o_sig
);
  logic q;
  always_ff @(posedge clk) begin
    q <= i_sig;
    cover (q);
  end
  assign o_sig = q;
endmodule
module dut_assignvar (
    input  logic i_sig,
    output logic o_sig
);
  logic var_q;
  assign var_q = i_sig;
  assign o_sig = var_q;
endmodule
import "DPI-C" function int c_dpi (input int a);
module dut_cfunc (
    input  logic [31:0] i_data,
    output logic [31:0] o_data
);
  always_comb begin
    o_data = c_dpi(i_data);
  end
endmodule
module dut_class (
    input  logic [7:0] i_data,
    output logic [7:0] o_data
);
  class MyClass;
    int data;
    function void set(int d); data = d; endfunction
    function int get(); return data; endfunction
  endclass
  always_comb begin
    MyClass c;
    c = new();
    c.set(i_data);
    o_data = c.get();
  end
endmodule
module dut_task (
    input  logic clk,
    input  logic [7:0] i_data,
    output logic [7:0] o_data
);
  task automatic do_add (
      input  logic [7:0] d,
      output logic [7:0] r
  );
    r = d + 8'h1;
  endtask
  always_ff @(posedge clk) begin
    do_add(i_data, o_data);
  end
endmodule
module dut_iface (
    input  logic clk,
    output logic o_data
);
  simple_if intf (clk);
  assign o_data = intf.a;
  always_ff @(posedge clk) begin
    intf.b <= o_data;
  end
endmodule
module dut_pkg (
    input  logic [31:0] i_val,
    output logic [31:0] o_val
);
  import my_pkg::*;
  logic [31:0] pkg_result;
  assign pkg_result = pkg_increment(int'(i_val));
  assign o_val = pkg_result;
endmodule
