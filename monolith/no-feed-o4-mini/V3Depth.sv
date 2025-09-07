module m_assign(input logic [3:0] a, b, c, d, e, output logic [3:0] y);
  assign y = ((a + b) * (c - d)) ^ e;
endmodule
module m_nested(input logic [7:0] a, b, c, d, output logic [7:0] y);
  assign y = ((((a & b) ^ c) | d) & ((a | b) ^ (c & d)));
endmodule
module m_func(input logic [3:0] a, b, output logic [3:0] y);
  function automatic logic [3:0] f;
    input logic [3:0] x, z;
    begin
      f = (x + ((z * x) - z));
    end
  endfunction
  function logic [3:0] g;
    input logic [3:0] p, q;
    begin
      g = ((p & q) | (p ^ q));
    end
  endfunction
  assign y = g(a, f(a, b));
endmodule
module m_task(input logic [3:0] a, b, output logic [3:0] y);
  task automatic t_calc;
    input logic [3:0] x;
    output logic [3:0] z;
    logic [3:0] tmp;
    begin
      tmp = (x + (x << 1));
      z = tmp * x;
    end
  endtask
  always_comb begin
    t_calc(a, y);
  end
endmodule
module m_case(input logic [1:0] sel, input logic [7:0] data, output logic [7:0] out);
  always_comb begin
    case (sel)
      2'b00: out = data;
      2'b01: out = ~data;
      default: out = data ^ (data << 1);
    endcase
  end
endmodule
module m_for(input logic [3:0] a, output logic [3:0] y);
  integer i;
  logic [3:0] sum;
  always_comb begin
    sum = 0;
    for (i = 0; i < a; i = i + 1)
      sum = sum + i;
  end
  assign y = sum;
endmodule
module m_while(input logic [3:0] a, output logic [3:0] y);
  logic [3:0] cnt;
  always_comb begin
    cnt = a;
    while (cnt > 0)
      cnt = cnt - 1;
  end
  assign y = cnt;
endmodule
module m_param(input logic sel, output logic [3:0] y);
  parameter logic [3:0] P0 = (2 + 3) * (4 - 1);
  localparam logic [3:0] LP = P0 + (1 << 2);
  assign y = sel ? P0 : LP;
endmodule
module m_struct(input logic [7:0] inbus, output logic [3:0] y);
  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } half_t;
  localparam half_t HCONST = '{hi:4'hC, lo:4'h3};
  assign y = HCONST.hi + inbus[3:0];
endmodule
module m_reduce(input logic [3:0] a, output logic y_and, output logic y_or, output logic y_xor);
  assign y_and = &a;
  assign y_or  = |a;
  assign y_xor = ^a;
endmodule
module m_generate(input logic clk, input logic rst, output logic [3:0] y);
  genvar i;
  logic [3:0] regs [0:3];
  generate
    for (i = 0; i < 4; i = i + 1) begin : genblk
      assign regs[i] = i;
    end
  endgenerate
  assign y = regs[0] + regs[1] + regs[2] + regs[3];
endmodule
