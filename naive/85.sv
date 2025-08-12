module comb_ops(input logic [3:0] a, input logic [3:0] b, output logic [3:0] y);
  always_comb begin
    logic [3:0] temp;
    temp = a & b;
    for (int i = 0; i < 4; i++) begin
      y[i] = temp[i] ^ a[3-i];
    end
  end
endmodule
module seq_reg(input logic clk, input logic rst, input logic [7:0] d, output logic [7:0] q);
  always_ff @(posedge clk) begin
    if (rst) q <= '0;
    else q <= d;
  end
endmodule
module latch_mod(input logic en, input logic d, output logic q);
  always_latch begin
    if (en) q = d;
  end
endmodule
module gen_array(input logic clk, input logic [1:0] sel, output logic [7:0] out);
  logic [7:0] arr [0:3];
  generate
    genvar i;
    for (i = 0; i < 4; i = i + 1) begin : gen_loop
      always_ff @(posedge clk) arr[i] <= i;
    end
  endgenerate
  assign out = arr[sel];
endmodule
module cond_gen #(parameter WIDTH = 4)(input logic [WIDTH-1:0] in, output logic [WIDTH-1:0] out);
  generate
    if (WIDTH <= 4) begin
      assign out = in << 1;
    end else begin
      assign out = in >> 1;
    end
  endgenerate
endmodule
module func_example(input logic [3:0] a, input logic [3:0] b, output logic [3:0] res);
  function logic [3:0] foo(input logic [3:0] x, input logic [3:0] y);
    foo = x + y;
  endfunction
  always_comb res = foo(a, b);
endmodule
module task_example(input logic clk, input logic en, input logic [7:0] in, output logic [7:0] out);
  logic [7:0] tmp;
  task automatic add_one(input logic [7:0] val, output logic [7:0] out_val);
    out_val = val + 1;
  endtask
  always_ff @(posedge clk) begin
    if (en) add_one(in, tmp);
    out <= tmp;
  end
endmodule
