class adder #(parameter int W = 8);
   function automatic logic [W-1:0] add(input logic [W-1:0] a,
                                        input logic [W-1:0] b);
      return a + b;
   endfunction
endclass
class shifter #(parameter int W = 8);
   function automatic logic [W-1:0] shiftl(input logic [W-1:0] a, input int s);
      return a << s;
   endfunction
   function automatic logic [W-1:0] shiftr(input logic [W-1:0] a, input int s);
      return a >> s;
   endfunction
endclass
module svmod00(input  logic [7:0] in0,
               output logic [7:0] out0);
   typedef struct packed {logic [3:0] lo; logic [3:0] hi;} swap_t;
   always_comb begin
      adder #(.W(8)) addObj = new();
      swap_t s = '{in0[3:0], in0[7:4]};
      out0 = addObj.add({s.hi, s.lo}, 8'h01);
   end
endmodule
module svmod01(input  logic        clk,
               input  logic [15:0] din,
               output logic [15:0] dout);
   typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;
   state_t state;
   always_ff @(posedge clk) begin
      shifter #(.W(16)) shObj = new();
      unique case (state)
         IDLE : begin
            dout  <= 16'h0;
            state <= RUN;
         end
         RUN  : begin
            dout  <= shObj.shiftl(din, 3);
            state <= DONE;
         end
         DONE : state <= IDLE;
      endcase
   end
endmodule
module svmod02(input  logic [3:0] a,
               input  logic [3:0] b,
               output logic [4:0] sum);
   always_comb begin
      adder #(.W(5)) a5 = new();
      sum = a5.add({1'b0, a}, {1'b0, b});
   end
endmodule
module svmod03 #(parameter int W = 12)
               (input  logic [W-1:0] x,
                input  logic [W-1:0] y,
                output logic [W-1:0] o);
   typedef union packed {logic [W-1:0] u; logic [W-1:0] v;} u_t;
   always_comb begin
      shifter #(.W(W)) sObj = new();
      u_t temp = '{default: x ^ y};
      o = sObj.shiftr(temp.u, 2);
   end
endmodule
module svmod04(input  logic        clk,
               input  logic        rst_n,
               input  logic [7:0]  data_in,
               output logic [7:0]  data_out);
   logic [7:0] buffer;
   always_ff @(posedge clk) begin
      if (!rst_n) buffer <= '0;
      else begin
         adder #(.W(8)) obj = new();
         buffer <= obj.add(data_in, 8'hAA);
      end
   end
   assign data_out = buffer;
endmodule
module svmod05(input  logic [31:0] din,
               output logic [31:0] dout);
   function automatic logic [31:0] reverse_bits(input logic [31:0] val);
      logic [31:0] rev;
      for (int i = 0; i < 32; i++) rev[i] = val[31 - i];
      return rev;
   endfunction
   always_comb begin
      shifter #(.W(32)) s = new();
      dout = s.shiftl(reverse_bits(din), 5);
   end
endmodule
class parity_c;
   function automatic logic [15:0] calc(input logic [15:0] v_in);
      logic pbit;
      pbit = ^v_in;
      return {15'h0, pbit};
   endfunction
endclass
module svmod06(input  logic [15:0] op,
               output logic [15:0] parity);
   always_comb begin
      parity_c pc = new();
      parity = pc.calc(op);
   end
endmodule
module svmod07(input  logic [7:0] a,
               output logic [7:0] z);
   typedef struct {logic [7:0] val;} wrap_t;
   wrap_t w;
   always_comb begin
      adder #(.W(8)) addi = new();
      w.val = a;
      z = addi.add(w.val, 8'h55);
   end
endmodule
module svmod08(input  logic        clk,
               input  logic [4:0]  idx,
               output logic [31:0] vec_out);
   logic [31:0] vec [0:31];
   initial begin
      for (int i = 0; i < 32; i++) vec[i] = i;
   end
   always_ff @(posedge clk) begin
      shifter #(.W(32)) sO = new();
      vec_out <= sO.shiftl(vec[idx], 1);
   end
endmodule
module svmod09(input  logic [23:0] din,
               output logic [23:0] dout);
   always_comb begin
      shifter #(.W(24)) sx = new();
      dout = sx.shiftr(din, 4);
   end
endmodule
module svmod10(input  logic [31:0] x,
               output logic [31:0] y);
   always_comb begin
      adder #(.W(32)) ax = new();
      y = ax.add(x, 32'h1);
   end
endmodule
module svmod11(input  logic clk,
               input  logic [7:0] a,
               output logic [7:0] q);
   always_ff @(posedge clk) begin
      adder #(.W(8)) obj = new();
      q <= obj.add(a, q);
   end
endmodule
module svmod12(input  logic [15:0] in1,
               input  logic [15:0] in2,
               output logic [15:0] out1);
   typedef struct packed {logic [7:0] l; logic [7:0] h;} s16;
   always_comb begin
      s16 x = '{in1[7:0], in2[15:8]};
      adder #(.W(8)) ob = new();
      out1 = {ob.add(x.l, x.h), 8'h0}[15:0];
   end
endmodule
module svmod13(input  logic [5:0] a,
               output logic [5:0] y);
   typedef enum logic [1:0] {EVEN, ODD} st_e;
   st_e st;
   always_comb begin
      adder #(.W(6)) ad = new();
      if (^a) st = ODD;
      else st = EVEN;
      y = (st == EVEN) ? ad.add(a, 6'd1) : ad.add(a, 6'd2);
   end
endmodule
module svmod14(input  logic [11:0] p,
               output logic [11:0] r);
   always_comb begin
      shifter #(.W(12)) s = new();
      r = s.shiftl(p, 2) ^ s.shiftr(p, 3);
   end
endmodule
module svmod15(input  logic       clk,
               input  logic [7:0] data,
               output logic [7:0] data_o);
   logic [7:0] regs[0:3];
   always_ff @(posedge clk) begin
      adder #(.W(8)) a = new();
      regs[0] <= data;
      regs[1] <= regs[0];
      regs[2] <= regs[1];
      regs[3] <= regs[2];
      data_o  <= a.add(regs[3], 8'h0F);
   end
endmodule
module svmod16(input  logic [9:0] vec,
               output logic [9:0] o);
   typedef struct packed {logic [4:0] lo; logic [4:0] hi;} halves_t;
   always_comb begin
      halves_t h = '{vec[4:0], vec[9:5]};
      shifter #(.W(10)) s = new();
      o = s.shiftl({h.hi, h.lo}, 1);
   end
endmodule
module svmod17(input  logic [31:0] a,
               output logic [31:0] b);
   function automatic logic [31:0] rotate_left(input logic [31:0] x_in);
      return {x_in[30:0], x_in[31]};
   endfunction
   always_comb begin
      b = rotate_left(a);
   end
endmodule
module svmod18(input  logic clk,
               input  logic rst_n,
               output logic flag);
   typedef enum logic {S0, S1} st_t;
   st_t st;
   always_ff @(posedge clk) begin
      if (!rst_n) begin
         st   <= S0;
         flag <= 1'b0;
      end else begin
         st   <= (st == S0) ? S1 : S0;
         flag <= ~flag;
      end
   end
endmodule
module svmod19(input  logic [15:0] din,
               output logic [7:0]  upper,
               output logic [7:0]  lower);
   assign upper = din[15:8];
   assign lower = din[7:0];
endmodule
module svmod20(input  logic [7:0] sel,
               output logic [7:0] onehot);
   always_comb begin
      onehot = 8'h0;
      if (sel < 8) onehot[sel] = 1'b1;
   end
endmodule
module svmod21(input  logic [7:0] in_val,
               output logic [3:0] popcnt);
   always_comb begin
      popcnt = $countones(in_val);
   end
endmodule
module svmod22(input  logic [31:0] a_in,
               input  logic [31:0] b_in,
               output logic [31:0] res);
   always_comb begin
      adder #(.W(32)) obj = new();
      res = obj.add(a_in & b_in, a_in | b_in);
   end
endmodule
module svmod23(input  logic clk,
               output logic [7:0] cnt);
   always_ff @(posedge clk) begin
      cnt <= cnt + 1'b1;
   end
endmodule
module svmod24(input  logic [15:0] raw,
               output logic [7:0]  hi,
               output logic [7:0]  lo);
   struct packed {logic [7:0] lo; logic [7:0] hi;} pword;
   always_comb begin
      pword = raw;
      hi = pword.hi;
      lo = pword.lo;
   end
endmodule
module svmod25(input  logic [7:0] x,
               output logic [7:0] y);
   logic [7:0] lut [0:255];
   initial for (int i = 0; i < 256; i++) lut[i] = i[7:0] ^ 8'hFF;
   assign y = lut[x];
endmodule
module svmod26(input  logic [11:0] angle,
               output logic signed [15:0] sine_approx);
   logic signed [15:0] lut [0:11];
   initial begin
      lut[0] = 0;    lut[1] = 1412; lut[2] = 2811; lut[3] = 4142;
      lut[4] = 5368; lut[5] = 6428; lut[6] = 7289; lut[7] = 7933;
      lut[8] = 8337; lut[9] = 8494; lut[10] = 8393; lut[11] = 8035;
   end
   assign sine_approx = lut[angle % 12];
endmodule
module svmod27(input  logic [7:0] in_byte,
               output logic [7:0] crc);
   logic [7:0] c;
   always_comb begin
      c = in_byte;
      repeat (8) c = (c[7]) ? (c << 1) ^ 8'h1D : (c << 1);
      crc = c;
   end
endmodule
module svmod28(input  logic clk,
               input  logic [7:0] din,
               output logic [7:0] dout);
   logic [7:0] mem [0:3];
   always_ff @(posedge clk) begin
      mem[0] <= din;
      mem[1] <= mem[0];
      mem[2] <= mem[1];
      mem[3] <= mem[2];
      dout   <= mem[3];
   end
endmodule
module svmod29(input  logic [31:0] in_a,
               input  logic [31:0] in_b,
               output logic [31:0] gcd);
   function automatic logic [31:0] gcd_func(input logic [31:0] x_val,
                                            input logic [31:0] y_val);
      logic [31:0] a_local;
      logic [31:0] b_local;
      a_local = x_val;
      b_local = y_val;
      while (b_local != 0) begin
         logic [31:0] t_local;
         t_local = b_local;
         b_local = a_local % b_local;
         a_local = t_local;
      end
      return a_local;
   endfunction
   assign gcd = gcd_func(in_a, in_b);
endmodule
module svmod30(input  logic [7:0] in_data,
               output logic [7:0] gray_code);
   assign gray_code = in_data ^ (in_data >> 1);
endmodule
module svmod31(input  logic [15:0] din,
               output logic [3:0]  lz);
   function automatic logic [3:0] lead_zero_count(input logic [15:0] val_arg);
      logic [3:0] count_local;
      count_local = 0;
      for (int i = 15; i >= 0; i--) begin
         if (val_arg[i] == 0) count_local = count_local + 1;
         else i = -1;
      end
      return count_local;
   endfunction
   always_comb begin
      lz = lead_zero_count(din);
   end
endmodule
