module mod_param #(parameter WIDTH = 8) (input logic [WIDTH-1:0] a, b, output logic [WIDTH-1:0] y);
  assign y = a ^ b;
endmodule
module mod_gen_if #(parameter SEL = 1) (input logic d0, d1, output logic y);
  generate
    if (SEL) assign y = d1;
    else      assign y = d0;
  endgenerate
endmodule
module mod_always_ff (input logic clk, rst, d, output logic q);
  always_ff @(posedge clk) begin
    if (rst) q <= 1'b0;
    else     q <= d;
  end
endmodule
module mod_always_latch (input logic e, d, output logic q);
  always_latch begin
    if (e) q = d;
  end
endmodule
module mod_function (input logic [7:0] in, output logic [7:0] out);
  function logic [7:0] invert;
    input logic [7:0] x;
    invert = ~x;
  endfunction
  assign out = invert(in);
endmodule
module mod_task (input logic ena, input logic [3:0] in, output logic [3:0] out);
  task automatic t;
    input  logic [3:0] a;
    output logic [3:0] b;
    b = a + 4'd1;
  endtask
  always_comb begin
    if (ena) t(in, out);
    else     out = in;
  end
endmodule
module mod_class (input logic clk, rst, output logic [3:0] q);
  class Counter;
    rand logic [3:0] cnt;
    function void inc(); cnt++;        endfunction
    function logic [3:0] get(); return cnt; endfunction
  endclass
  Counter c;
  always_ff @(posedge clk) begin
    if (rst) begin
      c = new();
      q <= 4'd0;
    end else begin
      c.inc();
      q <= c.get();
    end
  end
endmodule
interface bus_if (input logic clk, rst);
  logic [7:0] data;
  modport slave (input clk, rst, output data);
endinterface
module mod_interface (input logic clk, rst, output logic [7:0] q);
  bus_if intf(.clk(clk), .rst(rst));
  always_ff @(posedge clk) begin
    if (rst)    intf.data <= 8'd0;
    else        intf.data <= intf.data + 8'd1;
  end
  assign q = intf.data;
endmodule
module mod_assert (input logic clk, in, output logic out);
  always_ff @(posedge clk) out <= in;
  property p_seq; @(posedge clk) in |-> out; endproperty
  assert property (p_seq);
endmodule
module mod_cover (input logic clk, in, output logic dummy);
  covergroup cg @(posedge clk);
    cp: coverpoint in;
  endgroup
  cg cg_inst = new();
  always_ff @(posedge clk) dummy <= in;
endmodule
