module math_ops #(parameter WIDTH = 16)
   (input  logic [WIDTH-1:0]  in,
    output logic [WIDTH-1:0]  out);
   localparam logic [WIDTH-1:0] P_ADD = 16'd123 + 16'd77;
   localparam logic [WIDTH-1:0] P_SUB = 16'd999 - 16'd456;
   localparam logic [WIDTH-1:0] P_MUL = 16'd11  * 16'd9;
   localparam logic [WIDTH-1:0] P_DIV = 16'd987 / 16'd3;
   localparam logic [WIDTH-1:0] P_MOD = 16'd987 % 16'd10;
   localparam logic [WIDTH-1:0] P_POW = 16'd2   ** 8;
   assign out = in ^ P_ADD ^ P_SUB ^ P_MUL ^ P_DIV ^ P_MOD ^ P_POW;
endmodule
module shift_ops
   (input  logic [31:0] in,
    output logic [31:0] out);
   localparam logic [31:0] SLL = 32'h1 << 7;
   localparam logic [31:0] SRL = 32'hFF00_FF00 >> 5;
   localparam logic signed [31:0] SRA = 32'sh8000 >>> 4;
   assign out = (in | SLL) ^ (SRL ^ SRA);
endmodule
module reduce_ops
   (input  logic [7:0] in,
    output logic       out);
   localparam logic [7:0] CONST_VAL = 8'b10x1_1z0;
   always_comb begin
      logic red_or   = |CONST_VAL;
      logic red_and  = &CONST_VAL;
      logic red_xor  = ^CONST_VAL;
      logic one_hot  = $onehot(CONST_VAL);
      logic one_hot0 = $onehot0(CONST_VAL);
      logic is_unk   = $isunknown(CONST_VAL);
      int   cnt_ones = $countones(CONST_VAL);
      int   clog_val = $clog2(33);
      out = (red_or ^ red_and ^ red_xor ^ one_hot ^ one_hot0) & (~is_unk) ^ in[0] ^ cnt_ones[0] ^ clog_val[0];
   end
endmodule
module string_ops
   (input  logic [7:0] sel,
    output logic [7:0] out);
   always_comb begin
      string s1 = "Hello";
      string s2 = "World";
      string concat = {s1, " ", s2};
      int len;
      logic eq_bit;
      len = $strlen(concat);
      eq_bit = (s1 == s2);
      out = sel ^ len[7:0] ^ {7'b0, eq_bit};
   end
endmodule
module runtime_string_ops
   (input  logic [7:0] in,
    output logic [7:0] out);
   always_comb begin
      string s_local = "abc";
      s_local[1] = byte'(in);
      out = byte'(s_local[1]);
   end
endmodule
module real_ops
   (input  real in_real,
    output real out_real);
   localparam real R1 = 3.1415926535;
   localparam real R2 = 2.7182818284;
   always_comb begin
      real r_add;
      real r_sub;
      real r_mul;
      real r_div;
      real r_pow;
      logic [63:0] r_bits;
      real from_bits;
      int int_rnd;
      r_add = R1 + R2;
      r_sub = R1 - R2;
      r_mul = R1 * R2;
      r_div = R1 / 2.0;
      r_pow = R2 * R2;
      r_bits = $realtobits(R1);
      from_bits = $bitstoreal(r_bits);
      int_rnd = $rtoi(R2);
      out_real = in_real + r_add + r_sub + r_mul + r_div + r_pow + from_bits + int_rnd;
   end
endmodule
module class_use
   (input  logic clk,
    output logic [7:0] out);
   class Simple;
      int val;
      function new(int v); val = v; endfunction
      function int get(); return val; endfunction
   endclass
   always_comb begin
      Simple s = new(8);
      out = s.get()[7:0];
   end
endmodule
module convert_ops
   (input  logic [7:0]  in,
    output logic [15:0] out);
   always_comb begin
      int int_from_str = 9;
      logic [3:0] uns0 = 4'h0;
      logic [3:0] uns1 = 4'hF;
      logic [3:0] unsx = 4'hx;
      logic [3:0] unsz = 4'hz;
      logic signed [15:0] ext_s = $signed(-8'sd5);
      logic [15:0] repl_cat = {2{8'b1010_1100}};
      logic [31:0] sel_src = 32'hDEAD_BEEF;
      logic [7:0]  sel_part = sel_src[15:8];
      out = ({in, sel_part} ^ ext_s ^ repl_cat ^ int_from_str[15:0] ^ {uns0, uns1, unsx, unsz});
   end
endmodule
