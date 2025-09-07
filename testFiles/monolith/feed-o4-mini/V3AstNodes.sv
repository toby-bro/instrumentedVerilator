class RandCls;
  rand logic [3:0] a;
  rand logic [7:0] b;
  constraint c1 { a < 4; b inside {[0:3]}; }
endclass
module m_struct_union(input logic [7:0] data_in, output logic [7:0] data_out);
  typedef struct packed { logic [3:0] upper; logic [3:0] lower; } my_struct_t;
  typedef union packed { logic [7:0] whole; my_struct_t parts; } my_union_t;
  my_union_t u;
  always_comb begin
    u.parts.upper = data_in[7:4];
    u.parts.lower = data_in[3:0];
    data_out = u.whole;
  end
endmodule
module m_typedef_enum(input logic sel, output logic [1:0] code);
  typedef logic [1:0] code_t;
  typedef enum logic [2:0] { IDLE=3'd0, BUSY=3'd1, DONE=3'd2 } state_t;
  state_t st;
  always_comb begin
    if (sel) st = BUSY;
    else st = DONE;
    code = code_t'(st);
  end
endmodule
module m_array(input logic [7:0] in_arr [0:3], input logic [7:0] flat_in, output logic [7:0] out_arr [0:3]);
  logic [7:0] mem [0:3];
  always_comb begin
    mem[0] = flat_in;
    for (int i = 1; i < 4; i = i + 1) mem[i] = in_arr[i];
    out_arr = mem;
  end
endmodule
module m_generate_loop(input logic [3:0] in_bus, output logic [3:0] out_bus);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : genblk
      assign out_bus[i] = in_bus[i];
    end
  endgenerate
endmodule
module m_function_task(input logic clk, input logic [3:0] a, input logic [3:0] b, output logic [4:0] sum_out, output logic [3:0] diff_out);
  function automatic [4:0] func_add(input logic [3:0] x, input logic [3:0] y);
    func_add = x + y;
  endfunction
  task automatic task_sub(input logic [3:0] x, input logic [3:0] y, output logic [3:0] z);
    z = x - y;
  endtask
  always_ff @(posedge clk) begin
    sum_out <= func_add(a, b);
    task_sub(a, b, diff_out);
  end
endmodule
module m_class_rand(input logic clk, output logic [3:0] rand_val);
  RandCls rc;
  always_ff @(posedge clk) begin
    rc = new();
    assert(rc.randomize());
    rand_val <= rc.a;
  end
endmodule
module m_event(input logic trigger, output logic flag);
  event ev;
  always @(trigger) begin
    -> ev;
  end
  always @(ev) begin
    flag = 1'b1;
  end
endmodule
module m_clocking(input logic clk, input logic sig_i, output logic sig_o);
  clocking cb @(posedge clk);
    input sig_i;
    output sig_o;
  endclocking
  always @(cb) sig_o = cb.sig_i;
endmodule
module m_assert_cover(input logic clk, input logic [1:0] sel, output logic ok);
  always_ff @(posedge clk) begin
    assert(sel != 2'b11) else ok <= 1'b0;
    cover(sel == 2'b01);
    ok <= 1'b1;
  end
endmodule
import "DPI-C" function int dpi_mul(input int x, input int y);
module m_dpi(input int x, input int y, output int z);
  assign z = dpi_mul(x, y);
endmodule
module m_fork_join(input logic clk, input logic [3:0] in1, input logic [3:0] in2, output logic [3:0] out1, output logic [3:0] out2);
  always_ff @(posedge clk) begin
    fork
      out1 <= in1 + in2;
      out2 <= in1 - in2;
    join_none;
  end
endmodule
module m_dynamic(input logic clk, input logic [7:0] val, output logic [7:0] q_out, output logic [7:0] da_out);
  logic [7:0] da[];
  logic [7:0] queue[$];
  logic [7:0] assoc_map[string];
  always_ff @(posedge clk) begin
    da = new[2];
    da[0] = val;
    da[1] = val + 1;
    queue.push_back(val);
    assoc_map["foo"] = val;
    q_out <= queue.pop_front();
    da_out <= da[1];
  end
endmodule
module m_covergroup(input logic clk, input logic [1:0] sig, output logic ok);
  covergroup cg @(posedge clk);
    coverpoint sig {
      bins b0 = {2'b00};
      bins b1 = {2'b01, 2'b10};
    }
  endgroup
  cg cg_inst;
  always_ff @(posedge clk) begin
    cg_inst = new();
    cg_inst.sample();
    ok <= (sig == 2'b11);
  end
endmodule
