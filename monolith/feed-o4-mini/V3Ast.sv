module M_simpleFor(input logic [7:0] in, output logic [7:0] out);
  always_comb begin
    integer i;
    for (i = 0; i < 8; i = i + 1)
      out[i] = in[7 - i];
  end
endmodule
module M_ifElse(input logic [3:0] a, output logic y);
  always_comb begin
    if (a == 4'b0000)
      y = 1'b0;
    else if (a == 4'b1111)
      y = 1'b1;
    else
      y = ^a;
  end
endmodule
module M_caseStmt(input logic [1:0] sel, output logic [7:0] out);
  always_comb begin
    case (sel)
      2'b00: out = 8'hAA;
      2'b01: out = 8'h55;
      2'b10: out = {sel, sel, sel, sel};
      default: out = 8'hFF;
    endcase
  end
endmodule
module M_ternary(input logic en, input logic [7:0] a, input logic [7:0] b, output logic [7:0] y);
  assign y = en ? a : b;
endmodule
module M_concat(input logic [3:0] a, input logic [3:0] b, output logic [7:0] c);
  assign c = {a, b};
endmodule
module M_replicate(input logic [1:0] a, output logic [7:0] b);
  assign b = {4{a}};
endmodule
typedef struct packed { logic [3:0] f1; logic f2; } my_struct_t;
module M_structExample(input my_struct_t in_s, output my_struct_t out_s);
  always_comb out_s = in_s;
endmodule
typedef union packed { logic [3:0] u1; logic [3:0] u2; } my_union_t;
module M_unionExample(input my_union_t in_u, output my_union_t out_u);
  always_comb out_u = in_u;
endmodule
module M_parameterized #(parameter WIDTH = 4) (input logic [WIDTH-1:0] in_p, output logic [WIDTH:0] out_p);
  assign out_p = {{1{in_p[WIDTH-1]}}, in_p};
endmodule
module M_bitSlice(input logic [7:0] a, output logic [3:0] y);
  assign y = a[5:2];
endmodule
module M_functionExample(input logic [7:0] in_f, output logic [7:0] out_f);
  function automatic logic [7:0] myfunc(input logic [7:0] v);
    myfunc = v + 8'h1;
  endfunction
  always_comb out_f = myfunc(in_f);
endmodule
module M_taskExample(input logic a, output logic b);
  task automatic invert(input logic in_t, output logic out_t);
    out_t = ~in_t;
  endtask
  always_comb invert(a, b);
endmodule
module M_nestedLoops(input logic [3:0] in2, output logic [3:0] out2);
  always_comb begin
    integer i, j;
    logic tmp[3:0][3:0];
    for (i = 0; i < 4; i = i + 1) begin
      for (j = 0; j < 4; j = j + 1) begin
        tmp[i][j] = in2[i] & in2[j];
      end
    end
    out2 = tmp[2][3] ? in2 : {4{1'b0}};
  end
endmodule
module M_whileDo(input logic [3:0] in_w, output logic [3:0] out_w);
  always_comb begin
    integer cnt;
    cnt = 0;
    out_w = in_w;
    while (cnt < 4) begin
      out_w = out_w + cnt;
      cnt = cnt + 1;
    end
    do begin
      out_w = out_w - 1;
    end while (out_w > 0);
  end
endmodule
module M_generateExample(input logic en_g, output logic out_g);
  logic [3:0] w_g;
  genvar k;
  generate
    for (k = 0; k < 4; k = k + 1) begin : gen_loop
      assign w_g[k] = en_g & k[0];
    end
  endgenerate
  assign out_g = |w_g;
endmodule
module M_assertExample(input logic a1, input logic b1, output logic y1);
  always_comb begin
    assert (a1 | b1) else y1 = 1'b0;
    y1 = a1 & b1;
  end
endmodule
module M_classExample(input logic [3:0] in_c, output logic [3:0] out_c);
  class C;
    bit [3:0] val;
    function bit [3:0] inc(input bit [3:0] x);
      inc = x + 4'b0001;
    endfunction
  endclass
  always_comb begin
    static C c_inst = new();
    out_c = c_inst.inc(in_c);
  end
endmodule
module M_typeCast(input logic signed [7:0] a_cast, input logic unsigned [7:0] b_cast, output logic signed [7:0] out_cast);
  assign out_cast = a_cast + $signed(b_cast);
endmodule
module M_arrayExample(input logic [7:0] arr_in [0:3], output logic [7:0] arr_out [0:3]);
  genvar gi;
  generate
    for (gi = 0; gi < 4; gi = gi + 1) begin : arr_loop
      assign arr_out[gi] = arr_in[gi] ^ 8'hFF;
    end
  endgenerate
endmodule
module M_autoVar(input logic [3:0] a_av, output logic [3:0] out_av);
  always_comb begin
    automatic logic [3:0] tmp_var;
    tmp_var = a_av + 4'b0010;
    out_av = tmp_var;
  end
endmodule
