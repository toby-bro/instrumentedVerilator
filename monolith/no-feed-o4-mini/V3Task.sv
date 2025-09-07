module M1(input  logic a, input  logic b, output logic y);
  function logic f1(input logic x, input logic z);
    return x & z;
  endfunction
  task t1(input logic p, input logic q, output logic o);
    o = p | q;
  endtask
  always_comb begin
    logic tmp;
    tmp = f1(a, b);
    t1(a, b, y);
    y = y & tmp;
  end
endmodule
module M2(input  logic [31:0] in, output logic [31:0] out);
  import "DPI-C" function int dpi_add(input int a, input int b);
  assign out = dpi_add(in, 32);
endmodule
module M3(input  logic [7:0] din, output logic [7:0] dout);
  export "DPI-C" function sv_mul;
  function int sv_mul(input int val);
    return val * 2;
  endfunction
  assign dout = sv_mul(din);
endmodule
module M4(inout logic [3:0] bus, output logic [3:0] z);
  function logic [3:0] ref_inc(ref logic [3:0] x);
    return x + 1;
  endfunction
  always_comb begin
    z = ref_inc(bus);
  end
endmodule
module M5(input  logic [1:0][3:0] arr2d, output logic [3:0] res0, output logic [3:0] res1);
  function logic [3:0] sum_row(input logic [3:0] row);
    return row[0] + row[1] + row[2] + row[3];
  endfunction
  assign res0 = sum_row(arr2d[0]);
  assign res1 = sum_row(arr2d[1]);
endmodule
module M6(input  logic [3:0] iv, output logic [3:0] ov, output logic [7:0] sum);
  function logic [3:0] half(input logic [3:0] x);
    return x >> 1;
  endfunction
  function logic [7:0] add4(input logic [3:0] x);
    integer j;
    logic [7:0] acc;
    begin
      acc = 0;
      for (j = 0; j < 4; j = j + 1)
        acc = acc + x;
      return acc;
    end
  endfunction
  task iterative(input logic [3:0] in, output logic [3:0] out);
    integer i;
    out = in;
    i = 0;
    while (i < 4) begin
      out = half(out);
      i = i + 1;
    end
  endtask
  always_comb begin
    iterative(iv, ov);
    sum = add4(iv);
  end
endmodule
module M7 #(parameter WIDTH = 8) (input logic [WIDTH-1:0] in, output logic [WIDTH-1:0] inv);
  function logic [WIDTH-1:0] invert(input logic [WIDTH-1:0] x);
    return ~x;
  endfunction
  assign inv = invert(in);
endmodule
module M8(input  logic [1:0][1:0][3:0] mat, output logic [3:0] diag_sum);
  logic [3:0] a00, a11;
  assign a00 = mat[0][0];
  assign a11 = mat[1][1];
  assign diag_sum = a00 + a11;
endmodule
module M9(input  logic       in, inout wire        io, output logic       out);
  always_comb begin
    out = in & io;
  end
endmodule
