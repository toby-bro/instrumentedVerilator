package graph_pkg;
typedef enum logic [0:0] { FORWARD = 1'b0, REVERSE = 1'b1 } GraphWay;
class GraphPathChecker;
  logic [63:0] m_generation;
  logic [31:0] costOut;
  function new();
    m_generation = 0;
    costOut = 0;
  endfunction
  function void initHalfCriticalPaths(input GraphWay way, input bit checkOnly);
    if (way == FORWARD)
      costOut = 1;
    else
      costOut = 2;
  endfunction
  function bit pathExistsInternal(input bit ap, input bit bp, output int unsigned costp);
    costp = 1;
    return ap & bp;
  endfunction
  function bit pathExistsFrom(input bit fromp, input bit top);
    return fromp | top;
  endfunction
  function bit isTransitiveEdge(input bit e);
    return ~e;
  endfunction
endclass
endpackage
import graph_pkg::*;
module mod_initForward(input logic en, output logic [31:0] cost_out);
  GraphPathChecker gpc;
  always_comb begin
    gpc = new;
    gpc.initHalfCriticalPaths(FORWARD, en);
    cost_out = gpc.costOut;
  end
endmodule
module mod_initReverse(input logic en, output logic [31:0] cost_out);
  GraphPathChecker gpc;
  always_comb begin
    gpc = new;
    gpc.initHalfCriticalPaths(REVERSE, en);
    cost_out = gpc.costOut;
  end
endmodule
module mod_constructor(input logic trig, output logic ready);
  GraphPathChecker gpc;
  always_comb begin
    gpc = new;
    ready = 1'b1;
  end
endmodule
module mod_pathExistsInternal(input logic test, output logic found, output int unsigned cost_out);
  GraphPathChecker gpc;
  always_comb begin
    gpc = new;
    found = gpc.pathExistsInternal(test, 1'b1, cost_out);
  end
endmodule
module mod_pathExistsFrom(input logic go, output logic found);
  GraphPathChecker gpc;
  always_comb begin
    gpc = new;
    found = gpc.pathExistsFrom(go, 1'b0);
  end
endmodule
module mod_isTransitiveEdge(input logic sel, output logic isTrans);
  GraphPathChecker gpc;
  always_comb begin
    gpc = new;
    isTrans = gpc.isTransitiveEdge(sel);
  end
endmodule
