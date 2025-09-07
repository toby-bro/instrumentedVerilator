module mod_unique_if(input logic a, input logic b, input logic c, output logic [1:0] y);
  always_comb begin
    unique if (a)
      y = 2'b01;
    else if (b)
      y = 2'b10;
    else
      y = 2'b00;
  end
endmodule
module mod_case_simple(input logic [1:0] sel, input logic [7:0] d, output logic [7:0] y);
  always_comb begin
    case (sel)
      2'b00: y = d;
      2'b01: y = d + 1;
      default: y = 8'hFF;
    endcase
  end
endmodule
module mod_unique_casez(input logic [1:0] sel, output logic flag);
  always_comb begin
    unique casez (sel)
      2'b?0: flag = 1'b0;
      2'b?1: flag = 1'b1;
      default: flag = 1'bx;
    endcase
  end
endmodule
module mod_casex(input logic [3:0] in, output logic [1:0] sel);
  always_comb begin
    casex (in)
      4'b1xxx: sel = 2'b11;
      4'b01xx: sel = 2'b10;
      4'b001x: sel = 2'b01;
      default: sel = 2'b00;
    endcase
  end
endmodule
module mod_inside(input logic [3:0] val, output logic inside_flag);
  always_comb begin
    inside_flag = (val inside {4'h0,4'h3,4'h5,4'h6,4'h7});
  end
endmodule
module mod_onehot(input logic clk, input logic [2:0] sig, output logic ok);
  always_ff @(posedge clk) begin
    ok <= $onehot(sig);
  end
endmodule
module mod_onehot0(input logic clk, input logic [2:0] sig, output logic ok0);
  always_ff @(posedge clk) begin
    ok0 <= $onehot0(sig);
  end
endmodule
module mod_past(input logic clk, input logic a, input logic rst, output logic past_val);
  always_ff @(posedge clk) begin
    past_val <= $past(a,2);
  end
endmodule
module mod_assert_imm(input logic x, input logic y, output logic okimm);
  always_comb begin
    assert (x !== y);
    okimm = (x !== y);
  end
endmodule
module mod_assert_property(input logic clk, input logic p, input logic q, output logic okprop);
  property p_implication;
    @(posedge clk) disable iff (!q) p |-> q;
  endproperty
  assert property (p_implication);
  always_comb begin
    okprop = p && q;
  end
endmodule
module mod_assume_property(input logic clk, input logic p, input logic q, output logic okass);
  property p_seq;
    @(posedge clk) p |-> q;
  endproperty
  assume property (p_seq);
  always_comb begin
    okass = q;
  end
endmodule
module mod_cover_property(input logic clk, input logic sig, output logic covered);
  property p_cov;
    @(posedge clk) sig[*3];
  endproperty
  cover property (p_cov);
  always_comb begin
    covered = sig;
  end
endmodule
module mod_function(input logic [3:0] a, input logic [3:0] b, output logic [4:0] sum);
  function logic [4:0] add(input logic [3:0] x, input logic [3:0] y);
    add = x + y;
  endfunction
  always_comb begin
    sum = add(a,b);
  end
endmodule
module mod_generate(input logic [1:0] sel, input logic [7:0] din, output logic [7:0] dout);
  genvar i;
  generate
    for (i = 0; i < 2; i = i + 1) begin : genblk
      assign dout[i*4 +: 4] = (sel == i) ? din[i*4 +: 4] : 4'b0000;
    end
  endgenerate
endmodule
module mod_struct(input logic [7:0] in, output logic [7:0] out);
  typedef struct packed { logic [3:0] high; logic [3:0] low; } half;
  half data;
  always_comb begin
    data.high = in[7:4];
    data.low = in[3:0];
    out = {data.low, data.high};
  end
endmodule
