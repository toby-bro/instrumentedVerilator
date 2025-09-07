module NamedBeginExample(input logic a, output logic b);
  logic tmp;
  always_comb begin : blk1
    begin : blk2
      tmp = ~a;
    end
  end
  assign b = tmp;
endmodule
module ForkExample(input logic clk, input logic d, output logic q1, output logic q2);
  always_ff @(posedge clk) begin
    fork
      q1 <= d;
      q2 <= ~d;
    join
  end
endmodule
class MyClass;
  function int f(int x);
    return x * 2;
  endfunction
endclass
module ClassInstProc(input logic clk, input logic [3:0] in, output logic [4:0] out);
  always_ff @(posedge clk) begin : proc
    MyClass c = new();
    out <= c.f(in) + in;
  end
endmodule
module StaticFunctionExample(input logic [3:0] a, output logic [7:0] y);
  function automatic int sf(input int x);
    static int cnt = 0;
    cnt = cnt + 1;
    return cnt + x;
  endfunction
  assign y = sf(a);
endmodule
typedef logic [7:0] byte_t;
module TypedefExample(input logic [7:0] d, output logic [7:0] q);
  byte_t r;
  always_comb begin : named
    r = d;
  end
  assign q = r;
endmodule
interface MyIfc;
  logic sig;
endinterface
module InterfaceInstExample(input logic clk, input logic in_sig, output logic out_sig);
  MyIfc ifc();
  always_ff @(posedge clk)
    ifc.sig <= in_sig;
  assign out_sig = ifc.sig;
endmodule
module ForeachExample(input logic clk, input logic [7:0] din, output logic [7:0] sum);
  logic [7:0] arr [0:3];
  integer j, k;
  always_ff @(posedge clk) begin
    arr[0] <= din;
    foreach (arr[j]) arr[j] <= arr[(j+1)%4];
  end
  always_comb begin
    sum = 0;
    foreach (arr[k]) begin : loopblk
      sum = sum + arr[k];
    end
  end
endmodule
module DynQueueAssoc(input logic clk, input logic [7:0] din, output logic [31:0] cnt);
  logic [7:0] dyn_arr[];
  logic [7:0] queue_q[$];
  int assoc[int];
  initial begin
    assoc[0] = 10;
    assoc[1] = 20;
  end
  always_ff @(posedge clk) begin
    dyn_arr.push_back(din);
    queue_q.push_back(din);
  end
  integer idx, m, a;
  always_comb begin
    cnt = 0;
    foreach (dyn_arr[idx]) cnt = cnt + dyn_arr[idx];
    foreach (queue_q[m]) cnt = cnt + queue_q[m];
    foreach (assoc[a]) cnt = cnt + assoc[a];
  end
endmodule
module IfDepthExample(input logic a, b, c, output logic y);
  always_comb begin
    unique if (a) begin
      y = 1;
    end else if (b) begin
      y = 2;
    end else begin
      y = 3;
    end
    if (c) begin
      if (a) begin
        y = 4;
      end
    end
  end
endmodule
module CoverGroupExample(input logic clk, input logic [1:0] sig, output logic z);
  covergroup cg1 @(posedge clk);
    coverpoint sig;
  endgroup
  cg1 cg1_inst();
  always_ff @(posedge clk) begin
    z <= sig[0];
  end
endmodule
module GenerateLoopExample(input logic [3:0] in, output logic [3:0] out);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : genblk
      assign out[i] = in[i];
    end
  endgenerate
endmodule
module WhileLoopExample(input logic clk, output logic [3:0] cnt);
  always_ff @(posedge clk) begin
    int i = 0;
    cnt <= 0;
    while (i < 4) begin
      cnt <= cnt + i;
      i = i + 1;
    end
  end
endmodule
module TaskExample(input logic clk, input logic [3:0] a, output logic [4:0] y);
  task automatic tsk(input int x, output int yout);
    static int c = 0;
    c = c + 1;
    yout = x + c;
  endtask
  always_ff @(posedge clk)
    tsk(a, y);
endmodule
