package pkgs;
  typedef struct packed {
    logic [15:0] d;
  } my_t;
endpackage
class FwdClass;
  bit [7:0] data;
  function new(bit [7:0] d = 0);
    data = d;
  endfunction
endclass
class Outer;
  typedef struct packed {
    bit [7:0] q;
  } inner_t;
endclass
module forward_class_mod(
  input  logic clk,
  output logic valid
);
  FwdClass obj;
  always_ff @(posedge clk) begin
    if (obj == null) begin
      obj = new(8'h55);
    end
    valid <= (obj != null);
  end
endmodule
module package_struct_mod(
  input  logic [15:0] i,
  output pkgs::my_t   o
);
  assign o = '{d: i};
endmodule
module class_struct_mod(
  input  logic [7:0] i,
  output logic [7:0] o
);
  Outer::inner_t s;
  always_comb begin
    s.q = i;
    o   = s.q;
  end
endmodule
import "DPI-C" function int c_add(int a, int b);
module dpi_call_mod(
  input  logic [31:0] a,
  input  logic [31:0] b,
  output logic [31:0] sum
);
  int res;
  always_comb begin
    res = c_add(int'(a), int'(b));
    sum = res;
  end
endmodule
module child_mod(
  input  logic in,
  output logic out
);
  assign out = in;
endmodule
module cell_parent_mod(
  input  logic in,
  output logic out
);
  assign out = in;
endmodule
module class_return_mod(
  input  logic unsigned [7:0] in,
  output logic unsigned [7:0] out
);
  function automatic FwdClass mk(int v);
    FwdClass temp = new(logic[7:0]'(v & 8'hFF));
    return temp;
  endfunction
  FwdClass handle;
  always_comb begin
    handle = mk(int'(in));
    if (handle == null) begin
      out = 8'h00;
    end else begin
      out = handle.data;
    end
  end
endmodule
