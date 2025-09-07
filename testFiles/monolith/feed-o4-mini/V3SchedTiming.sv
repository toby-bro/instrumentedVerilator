module mod1(input logic a, output logic b);
  assign b = a;
endmodule
module mod2(input logic [3:0] din, output logic [3:0] dout);
  function automatic logic [3:0] f(input logic [3:0] x);
    f = x;
  endfunction
  assign dout = f(din);
endmodule
module mod3(input logic clk, input logic d, output logic q);
  always_ff @(posedge clk) begin
    q <= d;
  end
endmodule
module mod4(input logic clk, input logic a, output logic b);
  always_ff @(posedge clk) begin
    fork
      begin
        b <= a;
      end
    join
  end
endmodule
module mod5(input logic x, output logic y);
  always_comb begin : named
    y = ~x;
  end
endmodule
module mod6(input logic clk, input logic e, output logic f);
  always_ff @(posedge clk) begin
    wait (e);
    f <= e;
  end
endmodule
module mod7(input logic x, output logic y);
  task automatic t(input logic p, output logic r);
    r = p;
  endtask
  always_comb begin
    t(x, y);
  end
endmodule
module mod8(input logic [3:0] in, output logic [3:0] out);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin
      assign out[i] = in[i];
    end
  endgenerate
endmodule
module mod9(input logic [1:0] sel, output logic y);
  always_comb begin
    case (sel)
      2'b00: y = 1;
      default: y = 0;
    endcase
  end
endmodule
module mod10(input logic [3:0] init, output logic [3:0] y);
  class C;
    int v;
    function new(int init_v);
      v = init_v;
    endfunction
    function int get();
      return v;
    endfunction
  endclass
  C c_inst;
  always_comb begin
    c_inst = new(init);
    y = c_inst.get();
  end
endmodule
