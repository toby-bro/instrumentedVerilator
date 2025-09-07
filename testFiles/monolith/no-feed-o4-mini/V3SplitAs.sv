module split_always_example(input logic clk, input logic rst_n, input logic [7:0] din, output logic [7:0] dout);
  logic [7:0] a;
  logic [7:0] b;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      a <= 8'd0;
      b <= 8'd0;
    end else begin
      (* isolate_assignments *) a <= din + 1;
      b <= a << 1;
    end
  end
  assign dout = b;
endmodule
module func_call_example(input logic [3:0] x, input logic [3:0] y, output logic [3:0] z);
  logic [3:0] t;
  function automatic logic [3:0] fx(input logic [3:0] a, input logic [3:0] b);
    fx = a + b;
  endfunction
  always_comb begin
    t = fx(x, y);
  end
  assign z = t;
endmodule
class Cls;
  rand logic [7:0] data;
  function new();
    data = 8'hAA;
  endfunction
  function logic [7:0] get();
    return data;
  endfunction
endclass
module class_inst_example(input logic clk, input logic en, output logic [7:0] out);
  always_ff @(posedge clk) begin
    Cls c = new();
    if (en)
      out <= c.get();
    else
      out <= ~c.get();
  end
endmodule
module expression_example(input logic [3:0] a, input logic [3:0] b, input logic [3:0] c, output logic [7:0] y);
  logic [7:0] p;
  always_comb begin
    p = {a, b} + (((c[2:0] == 3'b101) ? 8'hFF : 8'h00) & ~({3{a}}));
  end
  assign y = p;
endmodule
module generate_example(input logic en, input logic [3:0] in, output logic [3:0] out);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : gen_loop
      assign out[i] = en ? in[i] : 1'b0;
    end
  endgenerate
endmodule
typedef struct packed { logic [3:0] f1; logic [3:0] f2; } mystruct_t;
typedef union packed { logic [7:0] u8; mystruct_t s; } myunion_t;
module struct_union_example(input logic [7:0] in, output logic [3:0] out1, output logic [3:0] out2);
  myunion_t u;
  always_comb begin
    u.u8 = in;
    out1 = u.s.f1;
    out2 = u.s.f2;
  end
endmodule
module always_types(input logic clk, input logic d, output logic q_comb, output logic q_ff, output logic q_latch);
  always_comb begin
    q_comb = d;
  end
  always_ff @(posedge clk) begin
    q_ff <= d;
  end
  always_latch begin
    if (d)
      q_latch = 1'b1;
    else
      q_latch = 1'b0;
  end
endmodule
module continuous_example(input logic a, input logic b, output logic y0, output logic y1);
  assign y0 = a & b;
  assign y1 = a | b;
endmodule
module assertion_example(input logic a, input logic b, input logic c, output logic z);
  always_comb begin
    z = (a & b) | c;
    assert (z | a);
  end
endmodule
