module shadow_var(input logic clk, input logic [7:0] in, output logic [7:0] out);
  logic [7:0] r;
  always_ff @(posedge clk) begin
    r <= in;
  end
  assign out = r;
endmodule
module shadow_var_masked(input logic clk, input logic [3:0] in_blk, input logic [3:0] in_nblk, output logic [7:0] out);
  logic [7:0] data;
  always_comb begin
    data[3:0] = in_blk;
  end
  always_ff @(posedge clk) begin
    data[3:0] <= in_nblk;
  end
  assign out = data;
endmodule
module flag_shared(input logic clk, input logic [7:0] val, input logic [1:0] index, output logic [7:0] out);
  logic [7:0] arr[0:3];
  always_ff @(posedge clk) begin
    arr[index] <= val;
  end
  assign out = arr[0];
endmodule
module flag_unique(input logic clk, input logic [7:0] in, output logic [7:0] out);
  logic [7:0] a;
  always_ff @(posedge clk) begin
    fork
      a <= in;
    join_none
  end
  assign out = a;
endmodule
module value_queue_whole(input logic clk, input logic [7:0] in, output logic [7:0] out);
  logic [7:0] arr[0:3];
  integer i;
  always_ff @(posedge clk) begin
    for(i = 0; i < 4; i = i + 1) begin
      arr[i] <= in;
    end
  end
  assign out = arr[2];
endmodule
module value_queue_partial(input logic clk, input logic [3:0] in, output logic [3:0] out);
  logic [7:0] arr[0:3];
  integer j;
  always_ff @(posedge clk) begin
    for(j = 0; j < 4; j = j + 1) begin
      arr[j][3:0] <= in;
    end
  end
  assign out = arr[1][3:0];
endmodule
module fire_event_example(input logic clk, input logic [7:0] in, output logic [7:0] out);
  logic trigger;
  event ev;
  always_ff @(posedge clk) begin
    trigger <= in[0];
  end
  always @(trigger) begin
    -> ev;
  end
  always_ff @(posedge ev) begin
    out <= in;
  end
endmodule
module queue_example(input logic clk, input logic [7:0] in, output logic [7:0] out);
  logic [7:0] dyn_queue[$];
  always_ff @(posedge clk) begin
    dyn_queue.push_back(in);
    if(dyn_queue.size() > 4)
      dyn_queue.pop_front();
  end
  assign out = dyn_queue.size() ? dyn_queue[0] : '0;
endmodule
module gen_example(input logic sel, input logic [7:0] a, input logic [7:0] b, output logic [7:0] out);
  generate
    if(sel) begin
      assign out = a;
    end else begin
      assign out = b;
    end
  endgenerate
endmodule
module func_task_example(input logic clk, input logic [7:0] in, output logic [7:0] out);
  function automatic [7:0] foo(input [7:0] x);
    foo = x + 1;
  endfunction
  task automatic bar(input [7:0] y, output [7:0] z);
    z = y - 1;
  endtask
  logic [7:0] tmp1, tmp2;
  always_ff @(posedge clk) begin
    tmp1 <= foo(in);
    bar(foo(in), tmp2);
    out <= tmp1 + tmp2;
  end
endmodule
module param_example#(parameter WIDTH = 8)(input logic [WIDTH-1:0] in, input logic clk, output logic [WIDTH-1:0] out);
  logic [WIDTH-1:0] reg_d;
  always_ff @(posedge clk) reg_d <= in;
  assign out = reg_d;
endmodule
interface my_if(input logic clk);
  logic [7:0] data;
  modport slave(input clk, output data);
endinterface
module inter_example(input my_if.slave bus, input logic [7:0] in, output logic [7:0] out);
  always_ff @(posedge bus.clk) begin
    bus.data <= in;
  end
  assign out = bus.data;
endmodule
