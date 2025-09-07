`timescale 1ns/1ps
module mod_timescale_format(input  logic in, output logic out);
  assign out = in;
endmodule
module mod_param_enum(input  logic [2:0] sel, output logic [3:0] out);
  parameter int WIDTH = 4;
  typedef enum logic [1:0] { A = 2'b00, B = 2'b01, C = 2'b10 } ETYPE;
  ETYPE e_sel;
  always_comb begin
    e_sel = ETYPE'(sel[1:0]);
    case (e_sel)
      A:       out = WIDTH;
      B:       out = WIDTH + B;
      default: out = sel + C;
    endcase
  end
endmodule
module mod_struct_sel(input  logic [3:0] idx, output logic [7:0] out);
  typedef struct packed { logic [7:0] a; logic [7:0] b; } SPK;
  typedef struct        { logic [7:0] u; logic [7:0] v; } UNSPK;
  SPK   spk_inst;
  UNSPK unspk_inst;
  always_comb begin
    spk_inst.a = idx;
    spk_inst.b = idx + 1;
    unspk_inst.u = spk_inst.b;
    unspk_inst.v = spk_inst.a;
    out = unspk_inst.v;
  end
endmodule
module mod_class_call(input  logic en, output logic [7:0] out);
  class MyClass;
    int member;
    function new(int init);
      member = init;
    endfunction
    function int add(input int x);
      return member + x;
    endfunction
  endclass
  MyClass inst1;
  MyClass inst2;
  always_comb begin
    inst1 = new(8);
    inst2 = new(16);
    out = inst1.add(inst2.member);
  end
endmodule
module mod_var_ref(input  logic [3:0] in, output logic [3:0] out);
  logic [3:0] local_var;
  always_comb begin
    local_var = in + 1;
    out = local_var;
  end
endmodule
module mod_array_ref(input  logic [1:0] idx, output logic [7:0] out);
  logic [7:0] arr [0:3] = '{8'hAA,8'hBB,8'hCC,8'hDD};
  always_comb out = arr[idx];
endmodule
module mod_cover(input  logic clk, input logic trig, output logic sigout);
  covergroup cg @(posedge clk);
    cp: coverpoint trig;
  endgroup
  cg cg_inst;
  initial begin cg_inst = new(); end
  always_ff @(posedge clk) cg_inst.sample();
  assign sigout = trig;
endmodule
module mod_function_static(input  logic clk, output logic [31:0] result);
  function int counter_fn();
    static int cnt = 0;
    cnt = cnt + 1;
    return cnt;
  endfunction
  always_ff @(posedge clk) result = counter_fn();
endmodule
