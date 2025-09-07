module enum_module(input logic in, output logic out);
  typedef enum logic [1:0] {E0=0, E1=1, E2=2, E3} my_enum_t;
  my_enum_t e = E2;
  assign out = (e == E2) ? in : 1'b0;
endmodule
module struct_module(input logic a, output logic [7:0] b);
  typedef struct packed { logic [3:0] s1; logic s2; } my_struct_t;
  my_struct_t s = '{4'hF, 1'b1};
  assign b = {s.s1, s.s2, 3'b000};
endmodule
module generate_module(input logic x, y, output logic z);
  genvar i;
  generate
    for (i = 0; i < 2; i = i + 1) begin : gb
      logic wi = x & y;
    end
    if (x) begin : gi
      logic wi2 = x | y;
    end else begin : ge
      logic wi2 = x ^ y;
    end
    case (y)
      1'b0: begin : gc0 logic w0 = x; end
      default: begin : gcd logic w1 = y; end
    endcase
  endgenerate
  assign z = gb[0].wi | gb[1].wi;
endmodule
module loops_module(input logic clk, input logic start, output logic done);
  logic [7:0] arr [0:3];
  always @(posedge clk) begin : loopblk
    int k;
    foreach (arr[k]) begin end
    repeat (3) begin end
    do begin end while (0);
    while (k < 0) begin k = k + 1; end
    wait (0);
  end
  assign done = start;
endmodule
module always_module(input logic a, b, output logic c);
  always_comb begin
    c = a & b;
    @(posedge a);
  end
endmodule
module class_module(input logic in, output logic out);
  import "DPI-C" function void dpi_func(input int a);
  class MyClass;
    int v = 0;
    function void method1;
      int tmp = v;
    endfunction
    function automatic int method2(input int x = 1);
      return x + v;
    endfunction
    constraint c { v inside {[0:10]}; }
  endclass
  MyClass mc;
  initial mc = new;
  always @(in) begin
    mc.method1();
    dpi_func(mc.method2(in));
  end
  assign out = mc.v;
endmodule
module attr_module(input logic a, output logic b);
  (* public_flat *) logic sig1;
  (* clock_enable *) logic sig2;
  typedef logic [7:0] type1;
  (* public *) type1 tvar;
  assign sig1 = a;
  assign b = sig1 & sig2;
endmodule
module param_module(input logic a, output logic b);
  parameter int P1;
  parameter int P2 = 5;
  logic pvar = P2;
  assign b = pvar & a;
endmodule
module ref_module(inout logic refsig, output logic ou);
  logic dflt = 1'b0;
  always @(*) refsig = dflt;
  assign ou = refsig;
endmodule
