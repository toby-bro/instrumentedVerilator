package util_pkg;
  function automatic int add_one(input int x);
    add_one = x + 1;
  endfunction
endpackage
interface if_with_modport;
  logic sig;
  task automatic t(input logic v);
    sig = v;
  endtask
  modport mp (import task t(input logic v), input sig);
endinterface
module alias_assignment_mod(
  input  wire in_sig,
  output wire out_sig
);
  alias out_sig = in_sig;
endmodule
module continuous_assign_mod#(
  parameter WIDTH = 8
)(
  input  wire [WIDTH-1:0] din,
  output wire [WIDTH-1:0] dout
);
  assign dout = din;
endmodule
module class_feature_mod(
  input  logic        clk,
  input  logic [31:0] value_in,
  output logic [31:0] value_out
);
  class myType;
    int val;
    function new(int v); val = v; endfunction
    function int get(); return val; endfunction
  endclass
  myType t;
  function automatic int scale(input int x);
    scale = x * 2;
  endfunction
  always_ff @(posedge clk) begin
    t = new(value_in);
    value_out <= scale(t.get());
  end
endmodule
module dpi_cfunc_mod(
  input  logic clk,
  input  int   a,
  input  int   b,
  output int   result
);
  import "DPI-C" function int c_add(input int a, input int b);
  always_ff @(posedge clk) begin
    result <= c_add(a, b);
  end
endmodule
module cover_toggle_mod(
  input  logic clk,
  input  logic sig_in,
  output logic sig_out
);
  always_ff @(posedge clk) begin
    cover(sig_in);
    sig_out <= sig_in;
  end
endmodule
module modport_task_ref_mod(
  input  logic clk,
  input  logic sig_in,
  output logic out_sig
);
  if_with_modport intf();
  always_ff @(posedge clk) begin
    intf.mp.t(sig_in);
    out_sig <= intf.sig;
  end
endmodule
module always_public_mod(
  input  logic in_sig,
  output logic out_sig
);
  always_comb out_sig = ~in_sig;
endmodule
