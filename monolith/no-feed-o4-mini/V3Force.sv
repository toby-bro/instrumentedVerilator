module mod_assign_force(input logic a_in, b_in, output logic a_out, b_out);
  logic a, b;
  assign a = a_in;
  assign b = b_in;
  initial begin
    force a = b;
    release a;
  end
  assign a_out = a;
  assign b_out = b;
endmodule
module mod_ternary(input logic [3:0] sel, input logic [3:0] d0, d1, output logic [3:0] q);
  wire [3:0] data;
  assign data = sel[0] ? d1 : d0;
  assign q = data;
endmodule
module mod_ff(input logic clk, rst, d, output logic q);
  always_ff @(posedge clk or posedge rst) begin
    if (rst) q <= 1'b0;
    else    q <= d;
  end
endmodule
module mod_comb(input logic [7:0] in1, in2, output logic [7:0] out1);
  always_comb begin
    out1 = in1 & in2;
  end
endmodule
module mod_func(input logic [1:0] idx, input logic [3:0] in, output logic [3:0] out);
  function logic [3:0] do_fn(input logic [3:0] v);
    do_fn = v ^ 4'hF;
  endfunction
  assign out = do_fn(in) + idx;
endmodule
module mod_task(input logic [3:0] in, output logic [3:0] out);
  task automatic do_task(input logic [3:0] vin, output logic [3:0] vout);
    begin
      vout = vin << 1;
    end
  endtask
  initial begin
    do_task(in, out);
  end
endmodule
module mod_generate(input logic [3:0] in, output logic [15:0] out);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : gen_blk
      assign out[i*4 +: 4] = in << i;
    end
  endgenerate
endmodule
module mod_coverprop(input logic clk, input logic sig, output logic out);
  cover property (@(posedge clk) sig);
  assign out = sig;
endmodule
module mod_part_select(input logic [7:0] in, output logic [3:0] out1, output logic out2);
  assign out1 = in[7:4];
  assign out2 = in[0];
endmodule
module mod_realcalc(input real a, input real b, output real y);
  always_comb begin
    y = a + b;
  end
endmodule
