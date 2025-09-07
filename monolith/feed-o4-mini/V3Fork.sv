module dynamic_scope_mod(input logic clk, input logic in, output logic out);
  class DynScopeClass;
    logic [7:0] a;
    logic [7:0] b;
    function new();
    endfunction
  endclass
  DynScopeClass ds;
  task automatic do_fork(input logic in_t);
    int x;
    x = in_t;
    fork
      begin
        ds = new();
        ds.a = x;
      end
      begin
        ds.b = ds.a + 1;
      end
    join_none
  endtask
  always_ff @(posedge clk) begin
    out <= in;
    do_fork(in);
  end
endmodule
module fork_any_mod(input logic in1, output logic out1);
  task automatic do_fork_any(input logic in_t, output logic out_t);
    fork
      out_t = in_t + 1;
      out_t = in_t - 1;
    join_any
  endtask
  always_comb begin
    do_fork_any(in1, out1);
  end
endmodule
module nested_fork_mod(input logic a, output logic b, output logic c);
  task automatic do_nested(input logic a_t, output logic b_t, output logic c_t);
    fork : outer
      begin
        b_t = a_t;
        fork : inner
          begin
            c_t = b_t;
          end
        join
      end
    join_none
  endtask
  always_comb begin
    do_nested(a, b, c);
  end
endmodule
module assign_delay_mod(input logic clk, input logic d, output logic q);
  always_ff @(posedge clk) begin
    q <= d;
  end
endmodule
module task_spawn_mod(input logic p, output logic r);
  task automatic tsk(input logic i, output logic o);
    o = i + 1;
  endtask
  task automatic tsk2(input logic i2, output logic o2);
    o2 = i2 * 2;
  endtask
  task automatic do_spawn(input logic p_t, output logic r_t);
    fork
      tsk(p_t, r_t);
      tsk2(p_t, r_t);
    join
  endtask
  always_comb begin
    do_spawn(p, r);
  end
endmodule
module event_mod(input logic clk, input logic in, output logic out);
  event e;
  logic internal;
  always_ff @(posedge clk) begin
    if (in)
      -> e;
  end
  always @(e) begin
    internal = 1'b1;
  end
  always_comb begin
    out = internal;
  end
endmodule
module struct_mod(input logic [7:0] in, output logic [3:0] out_high, output logic [3:0] out_low);
  typedef struct packed { logic [3:0] high; logic [3:0] low; } pair_t;
  pair_t pair_inst;
  always_comb begin
    pair_inst.high = in[7:4];
    pair_inst.low  = in[3:0];
    out_high       = pair_inst.high;
    out_low        = pair_inst.low;
  end
endmodule
module func_mod(input logic [3:0] in, output logic [3:0] out);
  function automatic logic [3:0] fn(input logic [3:0] a);
    fn = a + 1;
  endfunction
  always_comb begin
    out = fn(in);
  end
endmodule
module inout_mod(input logic en, output logic io);
  always_comb begin
    if (en)
      io = 1'b1;
    else
      io = 1'b0;
  end
endmodule
module class_simple_mod(input logic [7:0] a, output logic [7:0] b);
  class Simple;
    function automatic logic [7:0] inc(input logic [7:0] x);
      inc = x + 1;
    endfunction
  endclass
  Simple s;
  always_comb begin
    s = new();
    b = s.inc(a);
  end
endmodule
