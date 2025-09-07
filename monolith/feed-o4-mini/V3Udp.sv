primitive udp_comb3 (out, a, b, c);
  output out; input a, b, c;
  table
    1 1 1 : 1;
    1 0 1 : 0;
    0 1 0 : 1;
  endtable
endprimitive
primitive udp_seq2 (q, d);
  output reg q; input d;
  table
    (01) 0 : 0;
    1 1 : 1;
    0 1 : 1;
    1 0 : -;
  endtable
endprimitive
module use_comb(input logic a, b, c, output logic res);
  udp_comb3 u_comb(res, a, b, c);
endmodule
module use_seq(input logic d, output logic q);
  udp_seq2 u_seq(q, d);
endmodule
module nested_if(input logic a, b, c, output logic y);
  always_comb begin
    if (a) begin
      if (b & c)
        y = 1;
      else
        y = 0;
    end else
      y = 1'bx;
  end
endmodule
module bitwise_ops(input logic [3:0] in, output logic [3:0] out);
  assign out = (~in & (in << 1)) | (in ^ 4'hF);
endmodule
module event_ctrl(input logic clk, reset, data, output logic q);
  always @(posedge clk or negedge reset) begin
    if (!reset)
      q <= 0;
    else
      q <= data;
  end
endmodule
module func_cover(input logic [1:0] val,
                  output logic isEdge, isComb, isSeq,
                  output logic [0:0] oNum);
  function automatic logic isEdgeTrig(input logic [1:0] v);
    isEdgeTrig = (v == 2'b01) || (v == 2'b10);
  endfunction
  function automatic logic isCombOutSig(input logic [1:0] v);
    isCombOutSig = (v == 2'b00) || (v == 2'b01) || (v == 2'b10) || (v == 2'b11);
  endfunction
  function automatic logic isSeqOutSig(input logic [1:0] v);
    isSeqOutSig = isCombOutSig(v) || (v == 2'b10);
  endfunction
  function automatic logic [0:0] getOutputNum(input logic [1:0] v);
    case (v)
      2'b00: getOutputNum = 1'b0;
      2'b01: getOutputNum = 1'b1;
      default: getOutputNum = 1'bx;
    endcase
  endfunction
  assign isEdge = isEdgeTrig(val);
  assign isComb = isCombOutSig(val);
  assign isSeq  = isSeqOutSig(val);
  assign oNum   = getOutputNum(val);
endmodule
