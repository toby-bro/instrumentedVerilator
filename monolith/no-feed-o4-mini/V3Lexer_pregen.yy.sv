module basic_ops(input  logic [3:0] a, b,
                 output logic       and_out,
                 output logic       or_out,
                 output logic       eq_out,
                 output logic       case_eq_out,
                 output logic       lt_out,
                 output logic [3:0] plus_out);
  assign and_out      = a && b;
  assign or_out       = a || b;
  assign eq_out       = (a == b);
  assign case_eq_out  = (a === b);
  assign lt_out       = a < b;
  assign plus_out     = a + b;
endmodule
module edge_ctrl(input  logic clk, rst_n, in_sig,
                 output logic out_ff, out_latch);
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) out_ff <= 1'b0;
    else         out_ff <= in_sig;
  end
  logic latch_int;
  always_latch begin
    if (!rst_n) latch_int = 1'b0;
    else        latch_int = in_sig;
  end
  assign out_latch = latch_int;
endmodule
module multbit #(parameter WIDTH_IN=16, WIDTH_OUT=8)
                (input  logic [WIDTH_IN-1:0] data_in,
                 output logic [WIDTH_OUT-1:0] data_out);
  assign data_out = data_in[WIDTH_OUT-1:0];
endmodule
module generate_example(input  logic [3:0] in_array [0:3],
                        output logic       out_sum  [0:3]);
  genvar i;
  generate
    for (i=0; i<4; i=i+1) begin : sumgen
      logic tmp;
      assign tmp       = in_array[i] & 1'b1;
      assign out_sum[i] = tmp;
    end
  endgenerate
endmodule
module enum_typedef(input  logic [1:0] sel,
                    output logic       eq_signal);
  typedef enum logic [1:0] {IDLE=2'b00, RUN=2'b01, STOP=2'b10} state_t;
  state_t s, nxt;
  assign s   = state_t'(sel);
  assign nxt = (s == RUN) ? STOP : RUN;
  assign eq_signal = (s == nxt);
endmodule
module struct_union(input  logic sel,
                    output logic [7:0] uout,
                    string             sout);
  typedef struct packed { logic [3:0] a; logic [3:0] b; } two_nibbles;
  typedef union packed { logic [7:0] all; two_nibbles parts; } byte_f;
  byte_f u_reg;
  always_comb begin
    u_reg.parts.a = sel ? 4'hF : 4'h0;
    u_reg.parts.b = sel ? 4'h0 : 4'hF;
    sout = $sformatf("a=%0h b=%0h", u_reg.parts.a, u_reg.parts.b);
  end
  assign uout = u_reg.all;
endmodule
module dpi_example(input  int a,
                   output int b);
  import "DPI-C" function int c_add(input int x, input int y);
  always_comb b = c_add(a, 1);
endmodule
module class_example(input  logic clk, rst,
                     output logic rand_p);
  class c_test;
    rand bit [3:0] val;
    constraint c { val inside {4'h0, 4'hF}; }
    function void func(); endfunction
  endclass
  c_test inst;
  always_ff @(posedge clk or negedge rst) begin
    if (!rst)      inst = new();
    else           rand_p <= inst.randomize();
  end
endmodule
module cover_assume_example(input  logic clk, rst, sig,
                             output covergroup cg);
  covergroup cg @(posedge clk);
    cp: coverpoint sig { bins low = {0}; bins high = {1}; }
  endgroup
  cg cg_inst;
  always_ff @(posedge clk or negedge rst) begin
    if (!rst) cg_inst = new();
  end
endmodule
module assertion_example(input  logic clk, sig,
                         output logic ok1, ok2);
  property p1; @(posedge clk) sig |-> ##1 !sig; endproperty
  property p2; @(posedge clk) eventually sig; endproperty
  ok1 = 0; ok2 = 0;
  assert property (p1) else ok1 = 1;
  assume property (p2) else ok2 = 1;
endmodule
interface bus_if(input logic clk);
  logic       valid;
  logic [7:0] data;
  modport master (input data, valid);
endinterface
module interface_example(bus_if.master m_if,
                         input  logic [7:0] bus_data,
                         output logic       bus_valid);
  assign m_if.data  = bus_data;
  assign bus_valid  = m_if.valid;
endmodule
package pkg;
  import "DPI-C" function int add_dpi(input int x);
  typedef int my_int_t;
  localparam my_int_t MY_CONST = 1;
endpackage
module use_pkg(input pkg::my_int_t ip,
               output int           op);
  op = add_dpi(ip) + pkg::MY_CONST;
endmodule
program prog_example(input  logic start,
                     output logic done);
  always @(start) done = start;
endprogram
module cover_cross(input logic clk, sig1, sig2);
  covergroup cg @(posedge clk);
    cp1: coverpoint sig1;
    cp2: coverpoint sig2;
    cross cp_cross = {cp1, cp2};
  endgroup
  cg cg_inst;
  always_ff @(posedge clk) cg_inst = new();
endmodule
module seq_prop(input logic clk, a, b);
  sequence s1; a ##1 b; endsequence
  property p1; @(posedge clk) s1 |=> b; endproperty
  assert property (p1);
endmodule
`timescale 1ns/1ps
`default_nettype none
module config_example(input logic a, b, output logic c);
  parameter int P = 4;
  localparam int LP = P+1;
  assign c = (a ^ b) & LP[0];
endmodule
module typedef_example(input  logic [15:0] in,
                       output logic [7:0] out);
  typedef union packed { logic [7:0] byte; logic [3:0] half[1:0]; } u_t;
  u_t ureg;
  always_comb begin
    ureg.byte = in[7:0];
  end
  assign out = ureg.half[1];
endmodule
module params_example #(parameter WIDTH = 8)
                       (input  logic [WIDTH-1:0] din,
                        output logic [WIDTH-1:0] dout);
  localparam OFFSET = WIDTH/2;
  assign dout = din << OFFSET;
endmodule
endmodule
