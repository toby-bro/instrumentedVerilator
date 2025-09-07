package mypkg;
  typedef int pkg_int_t;
endpackage
module mod_string_ops(input logic [7:0] in_data, output logic [7:0] out_data);
  string s;
  function void str_ops(input string a, output string b);
    int L;
    L = a.len();
    if (L >= 3) b = a.substr(3, L-1);
    else b = "";
  endfunction
  always_comb begin
    s = "__PVT__name__DOT__value";
    string sa;
    str_ops(s, sa);
    out_data = in_data;
  end
endmodule
module mod_data_types(input logic clk, input logic rst_n, output logic [3:0] out);
  typedef enum logic [1:0] { STATE_IDLE, STATE_RUN, STATE_DONE } state_e;
  typedef struct packed { logic [3:0] a; logic [3:0] b; } mystruct_t;
  typedef union packed { logic [7:0] u; mystruct_t s; } myunion_t;
  state_e state;
  myunion_t udata;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) state <= STATE_IDLE;
    else state <= STATE_RUN;
  end
  assign out = udata.s.a;
endmodule
module mod_generate(input logic enable, output logic [7:0] sum_out);
  genvar i;
  logic [7:0] array [0:3];
  generate
    for (i = 0; i < 4; i++) begin : genblk
      assign array[i] = i * 2;
    end
  endgenerate
  always_comb begin
    sum_out = '0;
    for (int j = 0; j < 4; j++) sum_out += array[j];
  end
endmodule
class myclass;
  rand logic [3:0] x;
  function void do_something();
    x = x + 1;
  endfunction
endclass
module mod_class_inst(input logic clk, output logic [3:0] y);
  myclass c_inst;
  always_ff @(posedge clk) begin
    if (!c_inst) c_inst = new;
    c_inst.do_something();
    y <= c_inst.x;
  end
endmodule
module mod_tf(input logic a, input logic b, output logic f1, output logic f2);
  function logic fun_and(input logic x, input logic y);
    return x & y;
  endfunction
  task automatic task_or(input logic x, input logic y, output logic z);
    z = x | y;
  endtask
  always_comb begin
    f1 = fun_and(a, b);
    task_or(a, b, f2);
  end
endmodule
interface myif(input logic clk);
  logic sig;
  modport mp (input clk, output sig);
endinterface
module mod_if(input logic clk, myif.mp port_if, output logic o);
  always_ff @(posedge clk) begin
    port_if.sig <= ~port_if.sig;
  end
  assign o = port_if.sig;
endmodule
module mod_assert(input logic clk, input logic d, output logic q);
  always_ff @(posedge clk) begin
    q <= d;
    assert (d == q);
  end
  property p_eq; @(posedge clk) d == q; endproperty
  a_eq: assert property (p_eq);
endmodule
module mod_param#(parameter int WIDTH = 8)(input logic [WIDTH-1:0] a, output logic [WIDTH-1:0] b);
  localparam int OFFSET = WIDTH / 2;
  assign b = a >> OFFSET;
endmodule
module mod_pkg(input mypkg::pkg_int_t p, output mypkg::pkg_int_t q);
  assign q = p + 1;
endmodule
