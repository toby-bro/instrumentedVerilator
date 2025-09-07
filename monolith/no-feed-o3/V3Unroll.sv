package util_pkg;
  class dummy;
    int value;
    function new(int v = 0);
      value = v;
    endfunction
  endclass
endpackage
module loop_unroll #(
  parameter WIDTH = 8
) (
  input  logic [WIDTH-1:0] in_data,
  output logic [WIDTH+3:0] out_sum
);
  import util_pkg::*;
  always_comb begin : blk_loop_unroll
    dummy d = new(in_data);          
    int sum = 0;
    for (int i = 0; i < 8; i++) begin
      sum += d.value + i;
    end
    out_sum = sum;
  end
endmodule
module large_for (
  input  logic clk,
  output logic [15:0] parity
);
  import util_pkg::*;
  always_ff @(posedge clk) begin : blk_large_for
    dummy d = new(0);                
    int p = 0;
    for (int i = 0; i < 40; i++) begin
      p ^= (i ^ d.value);
    end
    parity <= p[15:0];
  end
endmodule
module gen_for_example #(
  parameter N = 4
) (
  input  logic [N-1:0] in_bus,
  output logic [N-1:0] out_bus
);
  genvar gi;
  generate
    for (gi = 0; gi < N; gi = gi + 1) begin : GEN_BLOCK
      assign out_bus[gi] = (gi % 2) ? ~in_bus[gi] : in_bus[gi];
    end
  endgenerate
endmodule
module while_unroll (
  input  logic clk,
  output logic [7:0] count_out
);
  import util_pkg::*;
  always_ff @(posedge clk) begin : blk_while_unroll
    dummy d = new(1);                
    int i  = 0;
    int acc = 0;
    while (i < 16) begin
      acc += d.value * i;
      i   = i + 1;
    end
    count_out <= acc[7:0];
  end
endmodule
module fork_example (
  input  logic in_a,
  output logic out_b
);
  always_comb begin : blk_fork
    fork
      out_b = in_a;
    join
  end
endmodule
module nested_for (
  input  logic [7:0] in_val,
  output logic [15:0] out_val
);
  always_comb begin : blk_nested_for
    int accum = 0;
    for (int i = 0; i < 4; i++) begin
      for (int j = 0; j < 3; j++) begin
        accum += in_val * (i + j);
      end
    end
    out_val = accum;
  end
endmodule
module modify_iterator (
  input  logic clk,
  output logic [7:0] result
);
  always_ff @(posedge clk) begin : blk_modify_iterator
    int i;
    int r = 0;
    for (i = 0; i < 10; i++) begin
      if (i == 5) i = i + 1; 
      r += i;
    end
    result <= r[7:0];
  end
endmodule
module while_module (
  input  logic clk,
  output logic [7:0] cnt
);
  always_ff @(posedge clk) begin : blk_while_module
    int k = 0;
    int c = 0;
    while (k < 12) begin
      c += k;
      k = k + 1;
    end
    cnt <= c[7:0];
  end
endmodule
