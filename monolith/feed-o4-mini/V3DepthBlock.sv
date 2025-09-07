module mod_debug(input logic [7:0] in, output logic [7:0] out);
  function automatic logic [7:0] debug(input logic [7:0] val);
    debug = ~val;
  endfunction
  assign out = debug(in);
endmodule
module mod_dumpLevel(input logic [7:0] in, output logic [3:0] out);
  function automatic logic [3:0] dumpTreeLevel(input logic [7:0] val);
    logic [3:0] i;
    begin
      dumpTreeLevel = 4;
      for (i = 0; i < 4; i = i + 1) begin
        if (val[i]) begin
          dumpTreeLevel = i;
        end
      end
    end
  endfunction
  assign out = dumpTreeLevel(in);
endmodule
module mod_dumpJson(input logic [3:0] in, output logic [3:0] out);
  function automatic logic [3:0] dumpTreeJsonLevel(input logic [3:0] val);
    logic [3:0] count;
    begin
      count = 0;
      while (count < val) begin
        count = count + 1;
      end
      dumpTreeJsonLevel = count;
    end
  endfunction
  assign out = dumpTreeJsonLevel(in);
endmodule
module mod_dumpEither(input logic in, output logic [7:0] out);
  function automatic logic [7:0] dumpTreeEitherLevel(input logic val);
    if (val) dumpTreeEitherLevel = 8'hAA;
    else       dumpTreeEitherLevel = 8'h55;
  endfunction
  assign out = dumpTreeEitherLevel(in);
endmodule
module mod_createDeepFunc(input logic [7:0] a, input logic [7:0] b, output logic [7:0] out);
  function automatic logic [7:0] createDeepFunc(input logic [7:0] x, input logic [7:0] y);
    logic [7:0] t1;
    logic [7:0] t2;
    begin
      t1 = x ^ y;
      begin
        t2 = (t1 & x);
        begin
          createDeepFunc = t2 | y;
        end
      end
    end
  endfunction
  assign out = createDeepFunc(a, b);
endmodule
module mod_visitModule #(parameter ENABLE = 1) (input logic [3:0] in, output logic [3:0] out);
  generate
    if (ENABLE) begin : visit_mod
      assign out = in + 1;
    end else begin : bypass
      assign out = in;
    end
  endgenerate
endmodule
module mod_visitCFunc(input logic [7:0] in, output logic [7:0] out);
  function automatic logic [7:0] visitCFunc(input logic [7:0] v);
    logic [7:0] tmp;
    begin
      tmp = v;
      for (int i = 0; i < 3; i = i + 1) begin
        tmp = tmp + i;
      end
      visitCFunc = tmp;
    end
  endfunction
  assign out = visitCFunc(in);
endmodule
module mod_visitStmtExpr(input logic [7:0] in, output logic [7:0] out);
  function automatic logic [7:0] visitStmtExpr(input logic [7:0] v);
    begin
      visitStmtExpr = v * v;
    end
  endfunction
  assign out = visitStmtExpr(in);
endmodule
module mod_visitJumpBlock(input logic [7:0] in, output logic [7:0] out);
  function automatic logic [7:0] visitJumpBlock(input logic [7:0] v);
    logic [7:0] cnt;
    begin
      cnt = v;
      while (cnt > 0 && cnt < 10) begin
        cnt = cnt - 1;
        if (cnt == 5) begin
          cnt = cnt + 2;
          break;
        end
      end
      visitJumpBlock = cnt;
    end
  endfunction
  assign out = visitJumpBlock(in);
endmodule
module mod_visitNodeStmt(input logic [7:0] in, output logic [7:0] out);
  function automatic logic [7:0] helper(input logic [7:0] v);
    helper = v + 1;
  endfunction
  function automatic logic [7:0] visitNodeStmt(input logic [7:0] v);
    logic [7:0] tmp;
    begin
      tmp = helper(v);
      visitNodeStmt = tmp << 1;
    end
  endfunction
  assign out = visitNodeStmt(in);
endmodule
module mod_visitNodeExpr(input logic [1:0] sel, output logic [7:0] out);
  always_comb begin
    case (sel)
      2'b00: out = 8'h00;
      2'b01: out = 8'h11;
      2'b10: out = 8'h22;
      default: out = 8'hFF;
    endcase
  end
endmodule
module mod_visitVar(input logic [3:0] in, output logic [7:0] out);
  logic [7:0] arr [0:3];
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : gen_vars
      assign arr[i] = in * i;
    end
  endgenerate
  assign out = arr[in[1:0]];
endmodule
module mod_visitNode(input logic [7:0] in, output logic [7:0] out);
  always_comb begin : node_block
    logic [7:0] temp;
    temp = in + 2;
    begin : inner
      temp = temp * 2;
      out = temp - 1;
    end
  end
endmodule
module mod_depthBlockAll(input logic clk, input logic rst, output logic [7:0] out);
  class DepthBlock;
    function automatic logic [7:0] depthBlockAll(input logic [7:0] v);
      depthBlockAll = v + 5;
    endfunction
  endclass
  DepthBlock db;
  always_comb begin
    db = new();
    out = db.depthBlockAll(rst ? 8'hFF : 8'h00) + clk;
  end
endmodule
