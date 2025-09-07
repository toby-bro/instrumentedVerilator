module M_IF(input  logic a, input  logic b, output logic [1:0] y);
unique if (a) y = 2'd1;
else if (b) y = 2'd2;
else y = 2'd3;
endmodule
module M_CASE(input  logic [1:0] sel, output logic out);
always_comb begin
 priority case (sel)
   2'd0: out = 1'b0;
   2'd1: out = 1'b1;
   2'd2: out = 1'b0;
   default: out = 1'b1;
 endcase
end
endmodule
module M_CASE2(input  logic [1:0] sel0, output logic out2);
always_comb begin
 unique0 case (sel0)
   2'd0: out2 = 1'b0;
   2'd1: out2 = 1'b1;
   default: out2 = 1'b0;
 endcase
end
endmodule
module M_PAST(input  logic clk, input logic rst, input logic inp, output logic p_out);
assign p_out = inp;
property PAL_PAST;
  @(posedge clk) disable iff (!rst) $past(inp,2);
endproperty
assert property (PAL_PAST);
endmodule
module M_SEQ(input  logic clk, input logic a, input logic b, output logic seq_out);
assign seq_out = a & b;
sequence AB_SEQ;
  a ##1 b;
endsequence
property AB_PROP;
  @(posedge clk) AB_SEQ;
endproperty
assert property (AB_PROP);
endmodule
module M_IMM_ASSERT(input logic x, output logic err);
always_comb begin
  err = 1'b0;
  assert (x) else err = 1'b1;
end
endmodule
module M_ASSERT_PROP(input logic clk, input logic p, input logic q, output logic o_ap);
assign o_ap = p;
property IMP_PROP;
  @(posedge clk) p |-> q;
endproperty
assert property (IMP_PROP);
endmodule
module M_ASSUME_COVER_RESTRICT(input logic clk, input logic rst, input logic x, output logic o_acr);
assign o_acr = x;
assume property (@(posedge clk) disable iff (!rst) x);
cover property  (@(posedge clk) x);
restrict property(@(posedge clk) x);
endmodule
module M_PROC_BEGIN(input logic a, output logic b);
begin : my_block
end
function logic f1(input logic v);
  begin
    return ~v;
  end
endfunction
task automatic t1(input logic in1, output logic out1);
  begin
    out1 = f1(in1);
  end
endtask
endmodule
module M_SENS(input logic clk, input logic d, output logic q);
always @(posedge clk or negedge d) begin
  q <= d;
end
endmodule
module M_COVER(input logic clk, input logic c, output logic cov);
assign cov = c;
cover property (@(posedge clk) c);
endmodule
module M_RESTRICT(input logic clk, input logic r, output logic ro);
assign ro = r;
restrict property (@(posedge clk) r);
endmodule
