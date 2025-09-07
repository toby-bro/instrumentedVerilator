`line 100 "m_line_directive.sv" 1
module m_line_directive(input logic [7:0] in, output logic [7:0] out);
  assign out = in;
endmodule
`line 200 "m_generate.sv" 2
module m_generate(input logic [3:0] sel, output logic [7:0] out);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : gen_loop
      assign out[i*2 +: 2] = sel[i] ? 2'b11 : 2'b00;
    end
  endgenerate
endmodule
`line 300 "m_gen_if.sv" 1
module m_gen_if(input logic sel, input logic [3:0] in, output logic [3:0] out);
  assign out = sel ? in : ~in;
endmodule
module m_types(input logic [1:0] sel, output logic [7:0] data);
  typedef enum logic [1:0] {E_IDLE, E_RUN, E_STOP, E_ERROR} state_t;
  typedef struct packed { logic a; logic [3:0] b; logic [2:0] pad; } mystruct_t;
  typedef union packed { logic [7:0] vec; mystruct_t s; } myunion_t;
  always_comb begin
    state_t curr;
    myunion_t u;
    case (sel)
      2'b00: curr = E_IDLE;
      2'b01: curr = E_RUN;
      2'b10: curr = E_STOP;
      default: curr = E_ERROR;
    endcase
    u.s.a = (curr == E_RUN);
    u.s.b = sel;
    u.s.pad = 3'b000;
    data = u.vec;
  end
endmodule
module m_class_usage(input logic clk, input logic rst, output logic [7:0] res);
  class calc;
    function int f(input int x);
      return x * x;
    endfunction
  endclass
  always_ff @(posedge clk) begin
    static calc c;
    if (c == null) c = new();
    res <= c.f(rst ? 1 : 2);
  end
endmodule
module m_random(input logic [2:0] rnd_in, output logic [4:0] rnd_out);
  class randc_cls;
    rand logic [4:0] a;
    constraint c1 { a inside {[0:10]}; }
    function void get(output logic [4:0] o);
      o = a;
    endfunction
  endclass
  always_comb begin
    randc_cls rc;
    rc = new();
    rc.randomize();
    rc.get(rnd_out);
  end
endmodule
module m_cover_assert(input logic [3:0] sig, input logic clk, output logic ok);
  covergroup cg @(posedge clk);
    cp : coverpoint sig;
  endgroup
  cg cg_h;
  always_ff @(posedge clk) begin
    if (!cg_h) cg_h = new();
    cg_h.sample();
    ok <= 1;
  end
  property p1 @(posedge clk);
    sig != 4'b0000;
  endproperty
  assert_p1: assert property(p1) else ok <= 0;
endmodule
interface if_t(input logic clk);
  logic [7:0] bus;
  modport mp (input clk, output bus);
endinterface
module m_if_inst(input logic clk, input logic [7:0] bus, output logic [7:0] odata);
  if_t my_if(.clk(clk));
  always_comb begin
    my_if.bus = bus;
    odata = my_if.bus;
  end
endmodule
import "DPI-C" function int dpi_func(input int a);
module m_dpi(input int a, output int b);
  assign b = dpi_func(a);
endmodule
module m_line_macro(input logic [3:0] x, output logic [3:0] y);
  localparam int L = `__LINE__;
  assign y = x + L;
endmodule
