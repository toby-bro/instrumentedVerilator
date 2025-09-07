module mod_debug(input logic en, output logic result);
  (* debug = "on" *) logic tmp;
  function logic _ZL5debugv(input logic a);
    return a;
  endfunction
  always_comb begin
    result = _ZL5debugv(en);
  end
endmodule
module mod_dump(input logic [1:0] level, output logic [7:0] out);
  function [3:0] _ZL13dumpTreeLevelv(input [1:0] lvl);
    case (lvl)
      2'b00: return 4'd0;
      2'b01: return 4'd1;
      2'b10: return 4'd2;
      default: return 4'd3;
    endcase
  endfunction
  function [7:0] _ZL17dumpTreeJsonLevelv(input integer lvl);
    logic [7:0] tmp;
    tmp = '0;
    for (int i = 0; i < lvl; i++) begin
      tmp[i] = 1'b1;
    end
    return tmp;
  endfunction
  always_comb begin
    out = {4'd0, _ZL13dumpTreeLevelv(level)} + _ZL17dumpTreeJsonLevelv(level);
  end
endmodule
module mod_findVisitor(input logic write, input logic rw, input logic attr, output logic found);
  class SplitAsFindVisitor;
    bit m_splitVscp;
    function new(); m_splitVscp = 1'b0; endfunction
    function void visitVarRef(input logic w, input logic r, input logic a);
      if ((w || r) && !m_splitVscp && a) m_splitVscp = 1'b1;
    endfunction
    function bit getSplit(); return m_splitVscp; endfunction
  endclass
  always_comb begin
    SplitAsFindVisitor visitor;
    visitor = new();
    visitor.visitVarRef(write, rw, attr);
    found = visitor.getSplit();
  end
endmodule
module mod_cleanVisitor(input logic write, input logic modeMatch, input logic [1:0] stmtVals, output logic keep);
  class SplitAsCleanVisitor;
    bit m_keepStmt;
    bit m_matches;
    bit m_modeMatch;
    function new(input bit mode); m_modeMatch = mode; m_keepStmt = 1'b0; m_matches = 1'b0; endfunction
    function void visitVarRef(input logic w);
      if (w) m_matches = 1'b1;
    endfunction
    function void visitNodeStmt(input logic stmtMatch);
      bit oldKeep = m_keepStmt;
      bit savedMatches = m_matches;
      m_matches = 1'b0;
      m_keepStmt = 1'b0;
      if (stmtMatch) m_matches = 1'b1;
      if (m_keepStmt || (m_modeMatch ? m_matches : !m_matches))
        m_keepStmt = 1'b1;
      else
        m_keepStmt = 1'b0;
      m_keepStmt = oldKeep || m_keepStmt;
      m_matches = savedMatches;
    endfunction
    function bit getKeep(); return m_keepStmt; endfunction
  endclass
  always_comb begin
    SplitAsCleanVisitor visitor;
    visitor = new(modeMatch);
    for (int i = 0; i < 2; i++) begin
      visitor.visitVarRef(write);
      visitor.visitNodeStmt(stmtVals[i]);
    end
    keep = visitor.getKeep();
  end
endmodule
module mod_splitVisitor(input logic clk, input logic rst, output logic done);
  class SplitAsVisitor;
    function new(); endfunction
    function void splitAlways(input logic nodein, input logic splitVscp, output int count);
      count = count + 1;
    endfunction
    function void visitAlways(input logic nodein, input logic splitVscp, output int count);
      bit localNode = nodein;
      while (!localNode) begin
        if (splitVscp) begin
          splitAlways(localNode, splitVscp, count);
          localNode = 1'b1;
        end else begin
          localNode = 1'b1;
        end
      end
    endfunction
  endclass
  SplitAsVisitor visitor;
  int splitCount;
  logic nodeFlag, splitFlag;
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      visitor = new();
      splitCount <= 0;
      nodeFlag <= 1'b0;
      splitFlag <= 1'b1;
    end else begin
      visitor.visitAlways(nodeFlag, splitFlag, splitCount);
    end
  end
  always_comb begin
    done = (splitCount > 0);
  end
endmodule
module mod_splitAsAll(input logic [1:0] level, output logic [1:0] stats);
  function logic _ZL19dumpTreeEitherLevelv(input [1:0] lvl);
    return (lvl == 2'd3);
  endfunction
  always_comb begin
    if (_ZL19dumpTreeEitherLevelv(level))
      stats = level;
    else
      stats = ~level;
  end
endmodule
module mod_types(input logic sel, input logic [3:0] in, output logic [3:0] out);
  typedef enum logic [1:0] { IDLE = 2'b00, RUN = 2'b01, DONE = 2'b10 } state_t;
  typedef struct { logic [3:0] a; logic [3:0] b; } pair_t;
  typedef union { logic [7:0] all; pair_t pr; } data_t;
  data_t data;
  state_t st;
  always_comb begin
    if (sel) begin
      data.pr.a = in;
      data.pr.b = ~in;
    end else begin
      data.all = {in, ~in};
    end
  end
  always_comb begin
    unique case (sel)
      1'b0: begin st = IDLE; out = data.pr.a; end
      1'b1: begin st = RUN; out = data.pr.b; end
    endcase
  end
endmodule
