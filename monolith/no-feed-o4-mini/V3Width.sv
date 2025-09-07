interface MyIfc;
  logic s;
  modport P(input s);
endinterface
module ArithmeticOps(input  logic [7:0] a, b,
                     output logic [7:0] sum, diff, prod, quot, rem);
  assign sum  = a + b;
  assign diff = a - b;
  assign prod = a * b;
  assign quot = a / b;
  assign rem  = a % b;
endmodule
module LogicalOps(input  logic x, y,
                  output logic land_o, lor_o, lxor_o, lnot_o);
  assign land_o = x && y;
  assign lor_o  = x || y;
  assign lxor_o = x ^ y;
  assign lnot_o = !x;
endmodule
module ComparisonOps(input  logic signed [3:0] sa, sb,
                     input  logic        [3:0] ua, ub,
                     output logic eqs, neqs, lts, gts, ltu, gtu);
  assign eqs = (sa == sb);
  assign neqs = (sa != sb);
  assign lts = (sa < sb);
  assign gts = (sa > sb);
  assign ltu = (ua < ub);
  assign gtu = (ua > ub);
endmodule
module ShiftOps(input  logic [7:0] din,
                input  logic [5:0] sh,
                output logic [7:0] sl, srl, sra);
  assign sl  = din << sh;
  assign srl = din >> sh;
  assign sra = din >>> sh;
endmodule
module ReduceOps(input  logic [7:0] vec,
                 output logic r_and, r_or, r_xor);
  assign r_and = &vec;
  assign r_or  = |vec;
  assign r_xor = ^vec;
endmodule
module ConcatRepOps(input  logic [3:0] hi, lo,
                    output logic [7:0] cat1, cat2, cat3);
  assign cat1 = {hi, lo};
  assign cat2 = {{2{1'b1}}, lo};
  assign cat3 = {2{lo}};
endmodule
module PartSelectOps(input  logic [7:0] data,
                     input  logic [2:0] idx,
                     output logic bit_sel,
                     output logic [3:0] slice_hi,
                     output logic [3:0] slice_lo);
  assign bit_sel   = data[idx];
  assign slice_hi  = data[7:4];
  assign slice_lo  = data[3:0];
endmodule
module ConditionalOps(input  logic       sel,
                      input  logic [3:0] d0, d1,
                      output logic [3:0] out);
  assign out = sel ? d0 : d1;
endmodule
module ParamModule #(
  parameter int WIDTH = 8
)(
  input  logic [WIDTH-1:0] pin,
  output logic [WIDTH-1:0] pout
);
  assign pout = pin << 1;
endmodule
module RealOps(input  real r1, r2,
               output real rr);
  assign rr = r1 + r2 * r1;
endmodule
module StringOps(input  string s,
                 input  int    idx, len,
                 output string sub,
                 output int    slen);
  assign sub  = s.substr(idx, len);
  assign sub  = s.toupper();
  assign slen = s.len();
endmodule
module CastOps(input  logic [3:0] a, b,
               output logic signed [3:0] so,
               output logic       [3:0] uo);
  assign so = $signed(a) + $signed(b);
  assign uo = $unsigned(a) + $unsigned(b);
endmodule
module InterfaceConn(input  MyIfc.P ifc,
                     output logic      f);
  assign f = ifc.s;
endmodule
module EventControl(input  logic clk, evt,
                    output logic flag);
  always_ff @(posedge evt) flag <= ~flag;
endmodule
module WaitControl(input  logic sig,
                   output logic out);
  always_ff @(posedge sig) begin
    out <= 1;
    wait (sig) out <= 0;
  end
endmodule
module GenerateFor(input  logic [7:0] arr [3:0],
                   input  logic       en,
                   output logic [3:0] out);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : GEN
      if (en)
        assign out[i] = arr[i][i +: 1];
      else
        assign out[i] = arr[i][3-i +: 1];
    end
  endgenerate
endmodule
module AssertCover(input  logic a, b);
  property p1; @(posedge a) b; endproperty
  assert property (p1);
  cover property (@(posedge a) disable iff (!b) a ##1 b);
endmodule
module RangeSelect(input  logic [15:0] data,
                   input  logic [3:0]  idx,
                   output logic [3:0]  rh, rl);
  assign rh = data[15:12];
  assign rl = data[idx +: 4];
endmodule
module ResizeOps(input  logic [7:0] in0,
                 output logic [3:0] out0,
                 output logic [15:0] out1);
  assign out0 = in0;   
  assign out1 = in0;   
endmodule
module ReplicateExpand(input  logic [3:0] in0,
                       output logic [7:0] ex0);
  assign ex0 = {{4{in0[3]}}, in0};
endmodule
typedef bit [3:0] nibble_t;
typedef union packed { nibble_t n; bit b; } utype_t;
module TypedefUnion(input utype_t u, output logic out);
  assign out = u.n[2];
endmodule
struct { logic [1:0] a; logic b; } us_t;
module UnpackedStruct(input us_t us, output logic [2:0] out);
  assign out = {us.a, us.b};
endmodule
interface Intf0;
  logic sig;
  modport M(input sig);
endinterface
module InterfaceMod(input Intf0.M ip, output logic op);
  assign op = ip.sig;
endmodule
module PackedStruct(input struct packed { logic [3:0] f1; logic f2; } ps,
                    output logic [4:0] out);
  assign out = {ps.f1, ps.f2};
endmodule
module GenerateCase(input  logic [1:0] sel,
                    input  logic a0, a1, a2,
                    output logic y0, y1, y2);
  generate
    case (sel)
      2'b00: assign y0 = a0;
      2'b01: assign y1 = a1;
      default: assign y2 = a2;
    endcase
  endgenerate
endmodule
