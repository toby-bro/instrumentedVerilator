package GraphPkg;
  typedef enum logic [0:0] { FORWARD = 1'b0, REVERSE = 1'b1 } GraphWay;
  function GraphWay invert(GraphWay way);
    invert = (way == FORWARD) ? REVERSE : FORWARD;
  endfunction
endpackage
class GraphPCNode;
  logic [31:0] m_cp [0:1];
  int unsigned m_seenAtGeneration;
  function new();
    for (int i = 0; i < 2; i++) m_cp[i] = 0;
    m_seenAtGeneration = 0;
  endfunction
endclass
module initPaths_FWD(input logic clk, input logic reset, input logic valid [0:2][0:2], input logic checkOnly, output logic [31:0] critOut);
  import GraphPkg::*;
  GraphPCNode nodes [0:2];
  initial for (int i = 0; i < 3; i++) nodes[i] = new();
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      critOut = 0;
    end else begin
      GraphWay way = FORWARD;
      GraphWay rev = invert(way);
      int idx = 0;
      while (idx < 3) begin
        int unsigned crit = 0;
        for (int j = 0; j < 3; j++) begin
          if (!valid[j][idx]) continue;
          int unsigned tmp = nodes[j].m_cp[way] + 1;
          if (tmp > crit) crit = tmp;
        end
        if (!checkOnly) nodes[idx].m_cp[way] = crit;
        idx++;
      end
      critOut = nodes[0].m_cp[way];
    end
  end
endmodule
module initPaths_REV(input logic clk, input logic reset, input logic adj [0:2][0:2], input logic checkOnly, output logic [31:0] critVal);
  import GraphPkg::*;
  GraphPCNode nodes [0:2];
  initial for (int i = 0; i < 3; i++) nodes[i] = new();
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      critVal = 0;
    end else begin
      GraphWay way = REVERSE;
      GraphWay rev = invert(way);
      int idx = 0;
      int unsigned localCrit;
      localCrit = 0;
      while (idx < 3) begin
        for (int j = 0; j < 3; j++) begin
          if (!adj[j][idx]) continue;
          int unsigned t = nodes[j].m_cp[way] + 1;
          localCrit = (t > localCrit) ? t : localCrit;
        end
        if (!checkOnly) nodes[idx].m_cp[way] = localCrit;
        idx++;
      end
      critVal = localCrit;
    end
  end
endmodule
module ctor_dtor(input logic clk, input logic reset, output logic [31:0] liveCount);
  GraphPCNode nodeList[$];
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      nodeList = {};
    end else begin
      nodeList.push_back(new GraphPCNode());
    end
    liveCount = nodeList.size();
  end
endmodule
module path_exists_internal(input logic [1:0] a, input logic [1:0] b, input logic start, output logic found, output logic [31:0] costOut);
  import GraphPkg::*;
  GraphPCNode nodes [0:3];
  int unsigned generation;
  function automatic logic pathExistsInternal(int unsigned ap, int unsigned bp, output int unsigned costp);
    GraphPCNode au = nodes[ap];
    GraphPCNode bu = nodes[bp];
    if (au.m_seenAtGeneration == generation) begin costp = 0; return 0; end
    au.m_seenAtGeneration = generation;
    costp = 1;
    if (ap == bp) return 1;
    if (au.m_cp[REVERSE] < bu.m_cp[REVERSE] + 1) return 0;
    if (bu.m_cp[FORWARD] < au.m_cp[FORWARD] + 1) return 0;
    logic fnd = 0;
    for (int unsigned e = 0; e < 4; e++) begin
      if (e == ap) continue;
      int unsigned childCost;
      if (pathExistsInternal(e, bp, childCost)) fnd = 1;
      costp += childCost;
    end
    return fnd;
  endfunction
  function automatic void doSearch(output logic res, output int unsigned cost);
    generation++;
    int unsigned c;
    res = pathExistsInternal(a, b, c);
    cost = c;
  endfunction
  always_comb begin
    if (start) doSearch(found, costOut);
    else begin found = 0; costOut = 0; end
  end
endmodule
module pathExistsFrom_mod(input logic start, input logic [1:0] fromp, input logic [1:0] top, output logic ok);
  int unsigned generation;
  function automatic void incGeneration();
    generation++;
  endfunction
  function automatic logic pathFrom(int unsigned a, int unsigned b);
    incGeneration();
    return (a == b);
  endfunction
  assign ok = start ? pathFrom(fromp, top) : 0;
endmodule
module isTransitiveEdge_mod(input logic [1:0] fromp, input logic [1:0] top, output logic trans);
  int unsigned generation;
  function automatic void incGen();
    generation++;
  endfunction
  function automatic logic simplePath(int unsigned f, int unsigned t);
    return (f < t);
  endfunction
  function automatic logic checkEdge(int unsigned f, int unsigned t);
    incGen();
    for (int unsigned e = 0; e < 4; e++) begin
      if (e == f) continue;
      if (simplePath(e, t)) return 1;
    end
    return 0;
  endfunction
  assign trans = checkEdge(fromp, top);
endmodule
