module mod_simple_assign(input [3:0] in, output [3:0] out);
  assign out = in;
endmodule
module mod_strength_assign(input a, output b);
  assign (strong1, weak0) b = a;
endmodule
module mod_force_release(input a, output b);
  reg tmp;
  always_comb begin
    force tmp = a;
    release tmp;
  end
  assign b = tmp;
endmodule
module mod_urandom(input clk, output reg [7:0] r);
  always_ff @(posedge clk) r <= $urandom;
endmodule
module mod_test_plusargs(input dummy, output out);
  assign out = $test$plusargs("foo");
endmodule
module mod_value_plusargs(input [7:0] in, output reg [7:0] out);
  reg [7:0] tmp;
  always_comb begin
    tmp = 8'h00;
    if ($value$plusargs("bar", tmp))
      out = tmp;
    else
      out = in;
  end
endmodule
module mod_prepost(input [3:0] in, output reg [3:0] postval, output reg eq_flag);
  reg [3:0] tmp;
  always_comb begin
    tmp = in;
    tmp = tmp + 1;
    postval = tmp;
    eq_flag = (tmp == tmp);
  end
endmodule
module mod_bit_sel(input [7:0] data, input [2:0] idx, output bitsel, output [3:0] rngsel);
  assign bitsel = data[idx];
  assign rngsel = data[7:4];
endmodule
module mod_struct(input [7:0] data, input dummy, output [7:0] f_out);
  typedef struct packed { bit [7:0] f; bit [1:0] g; } S_t;
  S_t s;
  always_comb begin
    s.f = data;
    s.g = 2'b00;
  end
  assign f_out = s.f;
endmodule
module mod_fn_call(input [7:0] a, input [7:0] b, output [7:0] out);
  function automatic [7:0] addfn(input [7:0] x, input [7:0] y);
    addfn = x + y;
  endfunction
  assign out = addfn(a, b);
endmodule
module mod_task_call(input [7:0] a, input [7:0] b, output reg [7:0] out);
  task automatic addtask(input [7:0] x, input [7:0] y, output [7:0] z);
    z = x + y;
  endtask
  always_comb begin
    addtask(a, b, out);
  end
endmodule
module mod_readmem(input en, output [7:0] out);
  reg [7:0] mem [0:15];
  initial $readmemh("data.hex", mem);
  assign out = en ? mem[0] : mem[1];
endmodule
module mod_constraint(input en, output reg [3:0] o);
  class C;
    rand bit [3:0] x;
    constraint c { x inside {[1:4]}; }
  endclass
  C c_inst;
  always_comb begin
    c_inst = new;
    if (en) c_inst.randomize();
    o = c_inst.x;
  end
endmodule
module mod_dist(input clk, output reg [31:0] dout);
  reg [31:0] seed_ff;
  reg [31:0] seed_dist;
  always_ff @(posedge clk) seed_ff <= seed_ff + 1;
  always_comb begin
    seed_dist = seed_ff;
    dout = $dist_uniform(seed_dist, 1, 10);
  end
endmodule
module mod_dist_tri(input clk, output real dout);
  int seed_ff;
  int seed_dist;
  always_ff @(posedge clk) seed_ff <= seed_ff + 1;
  always_comb begin
    seed_dist = seed_ff;
    dout = $dist_normal(seed_dist, 5, 1);
  end
endmodule
module mod_cell_array(input [2:0] idx, input dummy, output [7:0] out);
  reg [7:0] arr [0:7];
  assign out = dummy ? arr[idx] : arr[idx];
endmodule
