module deep_proc(input logic [7:0] a, b, output logic [7:0] y);
  always_comb begin : blk
    logic [7:0] tmp;
    tmp = (((a & b) | ~(a ^ b)) + ((a << 1) - (b >> 1)));
    y = tmp;
  end
endmodule
module func1(input logic [3:0] in, output logic [3:0] out);
  function automatic logic [3:0] f1(input logic [3:0] x);
    f1 = (x + 1);
  endfunction
  assign out = f1(in);
endmodule
module cls_proc(input logic clk, input logic rst, output logic out);
  class C;
    function int foo(int x);
      foo = x * x;
    endfunction
  endclass
  always_ff @(posedge clk) begin
    C c_inst;
    int tmp;
    c_inst = new();
    tmp = c_inst.foo(3);
    out <= tmp[0];
  end
endmodule
module repl(input logic [3:0] in, output logic [15:0] out);
  assign out = {4{in}};
endmodule
module tsk(input logic [1:0] in, output logic [1:0] out);
  task automatic t1(input logic [1:0] x, output logic [1:0] y);
    logic [1:0] z;
    z = (x + 2'b01);
    y = z;
  endtask
  always_comb begin
    t1(in, out);
  end
endmodule
module loop1(input logic [3:0] a, output logic [7:0] y);
  logic [7:0] sum;
  integer i;
  always_comb begin
    sum = 0;
    for (i = 0; i < 4; i = i + 1) begin
      sum = sum + a;
    end
    y = sum;
  end
endmodule
module sel_case(input logic [2:0] sel, input logic [7:0] a, output logic [7:0] y);
  always_comb begin
    if (sel == 3'b000)
      y = a;
    else if (sel == 3'b001)
      y = (a << 1);
    else
      case (sel)
        3'b010: y = (a >> 1);
        3'b011: y = (a + 1);
        default: y = 0;
      endcase
  end
endmodule
