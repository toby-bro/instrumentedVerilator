module mod_class #(parameter int P = 8) (input logic clk, input logic rst, output logic [31:0] out);
  class C;
    int a;
    function new(int init);
      this.a = init;
    endfunction
  endclass
  C c_inst;
  always_ff @(posedge clk) begin
    if (rst) begin
      c_inst = new(0);
      out <= 0;
    end else begin
      c_inst = new(P);
      out <= c_inst.a;
    end
  end
endmodule
module mod_param #(parameter int DP = 4) (input logic [DP-1:0] din, output logic [DP-1:0] dout);
  localparam int VAL = DP * 2;
  assign dout = din << 1;
endmodule
module mod_typedef (input logic clk, input logic rst, output logic [3:0] out);
  typedef struct packed { logic [1:0] a; logic [1:0] b; } st_t;
  st_t s;
  always_ff @(posedge clk) begin
    if (rst)
      s <= '0;
    else
      s <= '{a: s.b, b: s.a};
  end
  assign out = s.a;
endmodule
module mod_func (input logic [7:0] a, output logic [7:0] b);
  function automatic logic [7:0] f(input logic [3:0] x);
    f = x + 1;
  endfunction
  assign b = f(a[3:0]);
endmodule
module mod_local (input logic a, input logic b, output logic y);
  always_comb begin
    logic tmp;
    tmp = a & b;
    y = tmp;
  end
endmodule
module mod_gen_if (input logic sel, input logic a, input logic b, output logic out);
  genvar i;
  generate
    if (sel) begin : IFBLK
      assign out = a;
    end else begin : ELSEBLK
      assign out = b;
    end
  endgenerate
endmodule
module mod_gen (input logic in, output logic out);
  parameter int N = 4;
  wire [N-1:0] w;
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin : GENBLK
      assign w[i] = in;
    end
  endgenerate
  assign out = &w;
endmodule
module mod_nested (input logic in, output logic out);
  wire [1:0][1:0] w2;
  genvar i, j;
  generate
    for (i = 0; i < 2; i = i + 1) begin : lvl1
      for (j = 0; j < 2; j = j + 1) begin : lvl2
        assign w2[i][j] = in;
      end
    end
  endgenerate
  assign out = &w2;
endmodule
module mod_multi_dim (input logic [1:0] a, input logic [1:0][2:0] b, output logic [3:0] c);
  assign c = a + b[1];
endmodule
module mod_dpi_import (input logic [31:0] a, output logic [31:0] b);
  import "DPI-C" function int foo(input int x);
  assign b = foo(a);
endmodule
module mod_dpi_export (input logic [15:0] a, output logic [15:0] b);
  export "DPI-C" function glbl_fun;
  function int glbl_fun(input int x);
    glbl_fun = x + a;
  endfunction
  assign b = glbl_fun(a);
endmodule
