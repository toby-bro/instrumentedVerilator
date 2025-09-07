module FuncCoverage1(input logic [3:0] x, output logic [3:0] y);
  logic [3:0] temp;
  function automatic logic [3:0] debug;
    debug = x;
  endfunction
  function automatic void dumpLevel(input logic [3:0] lvl);
    temp = lvl + 1;
  endfunction
  function automatic void dumpJsonLevel(input logic [3:0] lvl);
    temp = lvl + 2;
  endfunction
  function automatic void dumpEitherLevel(input logic [3:0] lvl);
    temp = lvl + 3;
  endfunction
  always_comb begin
    y = debug();
    dumpLevel(x);
    dumpJsonLevel(x);
    dumpEitherLevel(x);
    y = temp;
  end
endmodule
module LoopWhile(input logic [3:0] cnt, output logic [5:0] sum_out);
  logic [5:0] sum;
  int i;
  always_comb begin
    sum = 0;
    i = 0;
    while (i < cnt) begin
      if (i == 2) begin
        i = i + 1;
        continue;
      end
      sum = sum + i;
      if (sum >= 5) begin
        break;
      end
      i = i + 1;
    end
    sum_out = sum;
  end
endmodule
module LoopDoWhile(input logic [3:0] inc, output logic [3:0] out_val);
  logic [3:0] tmp;
  int i;
  always_comb begin
    i = 0;
    do begin
      i = i + inc;
    end while (i < 10);
    tmp = i;
    out_val = tmp;
  end
endmodule
module LoopRepeat(input logic [3:0] rep, output logic [7:0] outp);
  logic [7:0] acc;
  always_comb begin
    acc = 0;
    repeat (rep) begin
      acc = acc + 1;
    end
    outp = acc;
  end
endmodule
module LoopForeach(input logic [7:0] arr [0:3], output logic [9:0] sumf);
  logic [9:0] s;
  int idx;
  always_comb begin
    s = 0;
    foreach (arr[idx]) begin
      s = s + arr[idx];
    end
    sumf = s;
  end
endmodule
module NamedBlockDisable(input logic a, input logic b, output logic [3:0] res);
  logic [3:0] t;
  always_comb begin : outer
    if (a) disable outer;
    t = 1;
  end
  assign res = t + (b ? 2 : 0);
endmodule
module ClassInstProc(input logic [3:0] vin, output logic [3:0] vout);
  class C;
    function automatic logic [3:0] meth(input logic [3:0] x);
      meth = x + 1;
    endfunction
  endclass
  C obj;
  always_comb begin
    obj = new;
    vout = obj.meth(vin);
  end
endmodule
module TaskVisitor(input logic [7:0] a, output logic [7:0] b);
  task automatic tsk(input logic [7:0] in, output logic [7:0] outp);
    outp = in + 1;
  endtask
  always_comb begin
    tsk(a, b);
  end
endmodule
module NamedBegin(input logic c, output logic y);
  always_comb begin : B1
    begin : B2
      y = c;
    end
  end
endmodule
