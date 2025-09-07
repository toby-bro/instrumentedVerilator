package pkg_test;
  typedef logic [7:0] pkg_t;
endpackage
interface simple_if(input logic clk);
  logic data;
endinterface
typedef struct packed { logic [3:0] a; logic [3:0] b; } my_t;
enum logic [1:0] states_e { IDLE, BUSY, DONE };
module class_module(input  logic clk, reset,
                    output logic [3:0] out);
  class counter;
    rand logic [3:0] val;
    function new();
      val = 0;
    endfunction
    function logic [3:0] inc();
      val = val + 1;
      return val;
    endfunction
  endclass
  logic [3:0] val_reg;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      val_reg <= 0;
    end else begin
      counter c = new();
      val_reg <= c.inc();
    end
  end
  assign out = val_reg;
endmodule
module interface_module(simple_if intf, input logic en, output logic ok);
  always_comb begin
    if (en) ok = intf.data;
    else    ok = ~intf.data;
  end
endmodule
module typedef_struct_module(input my_t in, output logic [4:0] sum);
  assign sum = in.a + in.b;
endmodule
module generate_module(input logic [7:0] in, output logic [7:0] out);
  genvar i;
  generate
    for (i = 0; i < 8; i = i + 1) begin : gen_loop
      if (i < 4) begin : gen_if
        assign out[i] = in[i];
      end else begin : gen_else
        assign out[i] = ~in[i];
      end
    end
  endgenerate
endmodule
module cover_module(input logic clk, input logic [1:0] sig, output logic [1:0] res);
  covergroup cg @(posedge clk);
    cp: coverpoint sig;
  endgroup
  cg cg_inst = new();
  assign res = sig;
endmodule
module function_task_module(input  logic [3:0] a, b,
                            output logic [3:0] sum, diff);
  assign sum  = add(a, b);
  assign diff = sub(a, b);
  function logic [3:0] add(input logic [3:0] x, input logic [3:0] y);
    add = x + y;
  endfunction
  task automatic sub(output logic [3:0] r, input logic [3:0] x, input logic [3:0] y);
    r = x - y;
  endtask
endmodule
module enum_struct_module(input logic clk, input states_e state,
                          input logic [3:0] din, output logic [3:0] dout);
  typedef struct packed { logic [3:0] x; states_e s; } s_t;
  s_t data_s;
  always_ff @(posedge clk) begin
    data_s.x <= din;
    data_s.s <= state;
  end
  assign dout = (data_s.s == IDLE) ? data_s.x :
                (data_s.s == BUSY) ? (data_s.x + 1) :
                                     (data_s.x - 1);
endmodule
module package_module(input pkg_test::pkg_t inp, output logic [7:0] outp);
  assign outp = inp;
endmodule
module param_module #(parameter int WIDTH = 8)
                     (input  logic [WIDTH-1:0] in, output logic [WIDTH-1:0] out);
  localparam int HALF = WIDTH / 2;
  generate
    if (HALF > 0) begin
      assign out = in << HALF;
    end else begin
      assign out = in;
    end
  endgenerate
endmodule
module union_module(input logic [31:0] data, output logic [7:0] low_byte, high_byte);
  union packed {
    logic [31:0] word;
    logic [7:0] bytes [3:0];
  } u;
  assign u.word      = data;
  assign low_byte    = u.bytes[0];
  assign high_byte   = u.bytes[1];
endmodule
module net_alias_module(input logic a, input logic b, output logic c);
  wire w      = a & b;
  wire awire  = w;
  assign c    = awire;
endmodule
