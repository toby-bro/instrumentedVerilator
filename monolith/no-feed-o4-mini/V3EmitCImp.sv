`timescale 1ns/1ps
`timeformat -unit 1ps -precision 0
module dynamic_new(input logic [7:0] din, output logic [7:0] dout);
  class MyDyn;
    function logic [7:0] inc(input logic [7:0] x);
      inc = x + 1;
    endfunction
  endclass
  always_comb begin
    MyDyn dyn = new();
    dout = dyn.inc(din);
  end
endmodule
module function_call(input logic [3:0] a, output logic [3:0] b);
  function logic [3:0] plus2(input logic [3:0] x);
    plus2 = x + 2;
  endfunction
  always_comb begin
    b = plus2(a);
  end
endmodule
module struct_sel(input struct packed { bit f1; logic [3:0] f2; } sin, output bit out);
  always_comb out = sin.f1;
endmodule
module nested_struct(input struct { struct { logic [1:0] i; } inner; } oin, output logic [1:0] oout);
  always_comb oout = oin.inner.i;
endmodule
module union_sel(input union packed { logic [3:0] a; logic [1:0] b; } uin, output logic [1:0] uout);
  always_comb uout = uin.b;
endmodule
module literal_text(input logic clk, output logic flag);
  localparam string txt = "hello vlSymsp world";
  always_comb flag = (txt != "");
endmodule
module param_defns #(parameter int WIDTH = 8, parameter signed OFFSET = -4)
                    (input logic [WIDTH-1:0] in, output logic signed [WIDTH-1:0] out);
  localparam int TOTAL = WIDTH + OFFSET;
  always_comb out = in + OFFSET;
endmodule
module generate_loop(input logic [15:0] in, output logic [15:0] out);
  genvar i;
  generate
    for (i = 0; i < 16; i = i + 1) begin : bit_rev
      assign out[i] = in[15-i];
    end
  endgenerate
endmodule
module associative_array_example(input logic [7:0] in, output logic [7:0] out);
  logic [7:0] arr[int];
  always_comb begin
    arr[in] = in + 1;
    out = arr[in-1];
  end
endmodule
module queue_example(input logic [7:0] din, output logic [7:0] dout);
  logic [7:0] q[$];
  always_comb begin
    q = {};
    q.push_back(din);
    dout = q.pop_front();
  end
endmodule
module case_if(input logic [1:0] sel, input logic [3:0] d, output logic [3:0] y);
  always_comb begin
    if (sel == 2'b00) begin
      y = d;
    end else begin
      case (sel)
        2'b01: y = d + 1;
        2'b10: y = d - 1;
        default: y = 0;
      endcase
    end
  end
endmodule
module enum_event(input logic trigger, output logic done);
  typedef enum logic [1:0] {E0, E1, E2} my_enum;
  my_enum state;
  event ev;
  always_comb begin
    state = trigger ? E1 : E0;
    done = (state == E1);
  end
endmodule
module class_method_call(input logic [4:0] a, output logic [4:0] b);
  class C3;
    function logic [4:0] addf(input logic [4:0] x);
      addf = x + 5;
    endfunction
  endclass
  always_comb begin
    C3 ptr = new();
    b = ptr.addf(a);
  end
endmodule
module member_and_struct(input logic [7:0] in, output logic [7:0] out);
  typedef struct { logic [3:0] hi; logic [3:0] lo; } half;
  typedef struct { half h; } whole;
  whole w;
  always_comb begin
    w.h.hi = in[7:4];
    w.h.lo = in[3:0];
    out = {w.h.lo, w.h.hi};
  end
endmodule
module covergroup_example(input logic [3:0] din, output logic [3:0] dout);
  covergroup cg @(posedge din[0]);
    coverpoint din;
  endgroup
  cg sample_cg = new();
  always_comb begin
    dout = din;
    sample_cg.sample();
  end
endmodule
module generate_if_gen(input logic en, input logic [7:0] in, output logic [7:0] out);
  generate
    if (en) begin : gen1
      assign out = in + 10;
    end else begin : gen2
      assign out = in - 10;
    end
  endgenerate
endmodule
module function_and_concat(input logic [3:0] a, input logic [3:0] b, output logic [7:0] y);
  function logic [7:0] concat4(input logic [3:0] x, input logic [3:0] z);
    concat4 = {x, z};
  endfunction
  always_comb y = concat4(a, b);
endmodule
module dynamic_array_example(input logic [3:0] len, input logic [7:0] din, output logic [7:0] dout);
  logic [7:0] da[];
  always_comb begin
    da = new[len];
    if (len > 0) da[len-1] = din;
    dout = (len > 0) ? da[0] : 0;
  end
endmodule
module nested_generate(input logic [1:0] sel, input logic [7:0] in, output logic [7:0] out);
  genvar i, j;
  generate
    for (i = 0; i < 2; i = i + 1) begin : L1
      for (j = 0; j < 4; j = j + 1) begin : L2
        if (sel == i) begin
          assign out[j + i*4] = in[j];
        end else begin
          assign out[j + i*4] = in[7-j];
        end
      end
    end
  endgenerate
endmodule
module hierarchical_ref(input logic [3:0] a, output logic [3:0] b);
  always_comb begin
    b = hierarchical_ref.a; 
  end
endmoduleendmodule
