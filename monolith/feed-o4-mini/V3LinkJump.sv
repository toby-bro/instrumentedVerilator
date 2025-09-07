module while_break_continue(input logic [3:0] a, output logic [3:0] b);
  always_comb begin
    int i;
    b = 0;
    i = 0;
    while (i < a) begin
      if (i == 2) break;
      if (i == 1) begin
        i = i + 1;
        continue;
      end
      b = b + i;
      i = i + 1;
    end
  end
endmodule
module do_while_loop(input logic en, output logic flag);
  always_comb begin
    logic tmp;
    tmp = en;
    do begin
      flag = tmp;
      tmp = ~tmp;
    end while (tmp);
  end
endmodule
module repeat_sum(input logic [3:0] count, output logic [7:0] sum);
  always_comb begin
    int i;
    sum = 0;
    i = 0;
    repeat (count) begin
      sum = sum + i;
      i = i + 1;
    end
  end
endmodule
module named_disable(input logic in, output logic out);
  always_comb begin: named_blk
    out = in;
    if (in) disable named_blk;
    out = ~in;
  end
endmodule
module func_return(input logic [7:0] a, output logic [7:0] b);
  always_comb begin
    b = myfunc(a);
  end
  function automatic logic [7:0] myfunc(input logic [7:0] x);
    logic [7:0] y;
    y = x;
    if (y == 0) return y;
    y = y + 1;
    return y;
  endfunction
endmodule
module task_return(input logic in, output logic out);
  always_comb begin
    task1(in, out);
  end
  task automatic task1(input logic i, output logic o);
    if (!i) begin
      o = 0;
      return;
    end
    o = 1;
  endtask
endmodule
module for_break_continue(input logic [3:0] in, output logic [3:0] out);
  always_comb begin
    int i;
    out = 0;
    for (i = 0; i < in; i++) begin
      if (i == 1) begin
        i = i + 1;
        continue;
      end
      if (i >= 3) break;
      out = out + i;
    end
  end
endmodule
module foreach_sum(input logic [7:0] mem [0:3], output logic [7:0] sum2);
  always_comb begin
    int i;
    sum2 = 0;
    foreach (mem[i]) begin
      sum2 = sum2 + mem[i];
    end
  end
endmodule
