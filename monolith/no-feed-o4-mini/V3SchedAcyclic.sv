module comb_loop2(input  logic in, output logic out);
  logic a, b;
  always_comb begin
    a = b & in;
    b = a | in;
  end
  assign out = a ^ b;
endmodule
module comb_loop3(input  logic in, output logic out);
  logic c1, c2, c3;
  always_comb c1 = c3 & in;
  always_comb c2 = c1 & in;
  always_comb c3 = c2 & in;
  assign out = c1 | c2 | c3;
endmodule
module no_loop(input  logic in, output logic out);
  assign out = in;
endmodule
module reg_with_loop(input  logic clk, input logic in, output logic out);
  logic r, a, b;
  always_ff @(posedge clk)
    r <= in;
  always_comb a = b;
  always_comb b = r & a;
  assign out = a;
endmodule
module vector_loop(input  logic [3:0] in, output logic [3:0] out);
  logic [3:0] v1, v2;
  always_comb v1 = v2 & in;
  always_comb v2 = v1 | in;
  assign out = v1 ^ v2;
endmodule
module one_bit(input  logic in, output logic out);
  logic x, y;
  always_comb x = in;
  always_comb y = x;
  assign out = y;
endmodule
module multi_fanout(input  logic [7:0] in, output logic [7:0] out);
  logic [7:0] m, p;
  always_comb m = in + 8'h1;
  always_comb p = m + in;
  assign out = p;
endmodule
module procedural_new(input  logic [3:0] in, output logic [3:0] out);
  class C;
    int x;
    function new(int i);
      x = i;
    endfunction
  endclass
  logic [3:0] tmp;
  always_comb begin
    C c = new(3);
    tmp = in + c.x;
  end
  assign out = tmp;
endmodule
module generate_loop(input  logic in, output logic out);
  genvar i;
  logic [1:0] tmp;
  generate
    for (i = 0; i < 2; i = i + 1) begin : gl
      always_comb tmp[i] = tmp[(i+1)%2] ^ in;
    end
  endgenerate
  assign out = tmp[0] & tmp[1];
endmodule
module func_loop(input  logic [4:0] in, output logic [4:0] out);
  function automatic logic [4:0] foo(input logic [4:0] x);
    foo = {x[3:0], x[4]};
  endfunction
  logic [4:0] a;
  always_comb a = foo(in);
  assign out = foo(a);
endmodule
