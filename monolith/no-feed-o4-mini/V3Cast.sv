module uniop_mod(input logic [7:0] a, output logic [7:0] y);
  assign y = ~a;
endmodule
module biop_mod(input logic signed [15:0] a, input logic signed [15:0] b, output logic signed [15:0] y);
  assign y = a + b;
endmodule
module cond_mod(input logic cond, input logic [3:0] a, input logic [3:0] b, output logic [3:0] y);
  assign y = cond ? a : b;
endmodule
module partsel_mod(input logic [31:0] in, input logic [4:0] base, input logic [4:0] width, output logic [31:0] y);
  assign y = in[base +: width];
endmodule
module quadop_mod(input logic [3:0] a, input logic [3:0] b, input logic [3:0] c, input logic [3:0] d, output logic [15:0] y);
  assign y = {a, b, c, d};
endmodule
module cast_mod(input logic signed [7:0] a, input logic [7:0] b, output logic signed [31:0] y_signed, output logic [31:0] y_unsigned);
  assign y_signed   = $signed(a);
  assign y_unsigned = $unsigned(b);
endmodule
module packmember_mod(input logic [3:0] in0, input logic [3:0] in1, output logic [3:0] y);
  typedef struct packed { logic [3:0] f0; logic [3:0] f1; } pack_t;
  pack_t p;
  assign p = '{in0, in1};
  assign y = p.f1;
endmodule
module exprstmt_mod(input logic a, input logic b, output logic y);
  always_comb begin
    a + b;
    y = a & b;
  end
endmodule
module negate_mod(input logic signed [7:0] a, output logic signed [7:0] y);
  assign y = -a;
endmodule
module varref_mod(input logic [7:0] in, output logic [7:0] y);
  logic [7:0] temp;
  assign temp = in;
  assign y    = temp;
endmodule
module const_mod(input logic dummy, output logic [7:0] y);
  assign y = 8'd42;
endmodule
module cmethodcall_mod(input logic [7:0] in, output logic [7:0] y);
  class C1;
    function logic [7:0] foo(logic [7:0] x);
      return x + 1;
    endfunction
  endclass
  always_comb begin
    C1 obj = new();
    y = obj.foo(in);
  end
endmodule
module cmethodhard_mod(input logic [7:0] in, output logic [7:0] y);
  class C2;
    static function logic [7:0] bar(logic [7:0] x);
      return x + 2;
    endfunction
  endclass
  always_comb begin
    y = C2::bar(in);
  end
endmodule
module membersel_mod(input logic [7:0] in, output logic [7:0] y);
  class C3;
    logic [7:0] m;
    function logic [7:0] get();
      return m;
    endfunction
  endclass
  always_comb begin
    C3 obj = new();
    obj.m = in;
    y     = obj.m;
  end
endmodule
module structsel_mod(input logic [3:0] in_a, input logic [3:0] in_b, output logic [3:0] y);
  typedef struct { logic [3:0] a; logic [3:0] b; } s_t;
  s_t s;
  assign s   = '{in_a, in_b};
  assign y   = s.b;
endmodule
module varex_mod(input logic [3:0] in, output logic [3:0] out);
  logic [3:0] var_;
  always_comb begin
    var_ = in;
    out  = var_;
  end
endmodule
