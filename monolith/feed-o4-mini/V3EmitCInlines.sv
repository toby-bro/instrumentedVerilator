module DynamicNew(input logic clk, input logic en, output logic done);
  class C;
    function void foo(); endfunction
  endclass
  C c;
  always_ff @(posedge clk) begin
    c = new;
    if (en)
      c.foo();
    done <= en;
  end
endmodule
module DistConstraints(input logic clk, input logic rst, output logic [3:0] result);
  class DistClass;
    rand logic [3:0] a;
    rand logic [3:0] b;
    constraint c1 { a dist { [0:3] :/ 1, [4:7] :/ 3 }; }
    constraint c2 { b dist { [0:1] :/ 1, [2:3] :/ 2, [4:7] :/ 3 }; }
  endclass
  DistClass d;
  logic [7:0] temp;
  always_ff @(posedge clk) begin
    if (!rst) begin
      d = new;
      d.randomize();
      temp <= d.a + d.b;
    end else
      temp <= 0;
  end
  assign result = temp[3:0];
endmodule
module GenericOps(input logic a, input logic b, input logic sel, input logic [3:0] in1, input logic [3:0] in2, output logic [3:0] out1, output logic [3:0] out2);
  assign out1 = in1 + in2;
  assign out2 = sel ? in1 : in2;
endmodule
module ComplexGen #(parameter int N = 4) (input logic clk, input logic rst, output logic q);
  logic [N-1:0] arr;
  genvar i;
  generate
    if (N > 2) begin : if_blk
      for (i = 0; i < N; i = i + 1) begin : gen_loop
        assign arr[i] = (i % 2) ? 1'b1 : 1'b0;
      end
    end
  endgenerate
  always_ff @(posedge clk) begin
    if (!rst)
      q <= arr[N-1] ^ q;
    else
      q <= 0;
  end
endmodule
typedef struct packed { logic [7:0] a; logic [3:0] b; } mystruct_t;
typedef union packed { logic [3:0] u1; logic [3:0] u2; } myunion_t;
typedef enum logic [1:0] { IDLE = 2'b00, BUSY = 2'b01, DONE = 2'b10 } state_t;
module TypeUse(input logic [7:0] in_a, input logic [3:0] in_b, output mystruct_t s_out, output myunion_t u_out, output state_t st_out);
  mystruct_t s;
  myunion_t u;
  state_t st;
  always_comb begin
    s.a = in_a;
    s.b = in_b;
    u.u1 = in_b;
    u.u2 = in_b;
    if (in_a == 0)
      st = IDLE;
    else if (in_a > 128)
      st = BUSY;
    else
      st = DONE;
  end
  assign s_out = s;
  assign u_out = u;
  assign st_out = st;
endmodule
interface bus_if(input logic clk);
  modport m(input clk);
endinterface
module InterfaceUse(input logic clk_in, output logic out);
  bus_if bus_if_inst(.clk(clk_in));
  always_comb begin
    out = bus_if_inst.clk;
  end
endmodule
