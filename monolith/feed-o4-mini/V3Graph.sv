module UnlinkEdgesMod(input logic clk, input logic en, output logic done);
  class Edge;
    function new(); endfunction
    function void unlinkDelete(); endfunction
  endclass
  class Vertex;
    Edge outs[$];
    Edge ins[$];
    function new(); endfunction
    function void unlinkEdges();
      Edge ep;
      while (outs.size() > 0) begin
        ep = outs.pop_front();
        ep.unlinkDelete();
      end
      while (ins.size() > 0) begin
        ep = ins.pop_front();
        ep.unlinkDelete();
      end
    endfunction
  endclass
  always_ff @(posedge clk) if (en) begin
    Vertex v;
    Edge e1;
    Edge e2;
    v = new Vertex();
    e1 = new Edge();
    v.outs.push_back(e1);
    e2 = new Edge();
    v.ins.push_back(e2);
    v.unlinkEdges();
    done <= 1;
  end
endmodule
module RerouteEdgesMod(input logic clk, input logic st, output logic done);
  class GraphVertex;
  class GraphEdge;
    GraphVertex m_fromp;
    GraphVertex m_top;
    int weight;
    bit cutable;
    function new(GraphVertex f, GraphVertex t, int w, bit c);
      m_fromp = f;
      m_top    = t;
      weight   = w;
      cutable  = c;
    endfunction
    function GraphVertex fromp();
      return m_fromp;
    endfunction
    function GraphVertex top();
      return m_top;
    endfunction
    function void unlinkDelete(); endfunction
  endclass
  class GraphVertex;
    GraphEdge inE[$];
    GraphEdge outE[$];
    function new(); endfunction
    function void unlinkEdges();
      GraphEdge ep;
      while (outE.size() > 0) begin
        ep = outE.pop_front();
        ep.unlinkDelete();
      end
      while (inE.size() > 0) begin
        ep = inE.pop_front();
        ep.unlinkDelete();
      end
    endfunction
    function void rerouteEdges();
      int i;
      int j;
      for (i = 0; i < inE.size(); i = i + 1) begin
        for (j = 0; j < outE.size(); j = j + 1) begin
          GraphEdge e;
          e = new GraphEdge(inE[i].fromp(), outE[j].top(),
                            (inE[i].weight < outE[j].weight ? inE[i].weight : outE[j].weight),
                            inE[i].cutable && outE[j].cutable);
        end
      end
      unlinkEdges();
    endfunction
  endclass
  always_ff @(posedge clk) if (st) begin
    GraphVertex v;
    GraphVertex v1;
    GraphVertex v2;
    GraphEdge e1;
    GraphEdge e2;
    v  = new GraphVertex();
    v1 = new GraphVertex();
    v2 = new GraphVertex();
    e1 = new GraphEdge(v1, v2, 3, 1);
    v.inE.push_back(e1);
    e2 = new GraphEdge(v2, v1, 4, 0);
    v.outE.push_back(e2);
    v.rerouteEdges();
    done <= 1;
  end
endmodule
module FindEdgeMod(input logic clk, input logic st, output logic found);
  class Vertex;
    int aEdges[$];
    int bEdges[$];
    function new(); endfunction
    function int findConnectingEdgep(Vertex w);
      int aSize;
      int bSize;
      int ai;
      int bi;
      aSize = aEdges.size();
      bSize = w.bEdges.size();
      ai = 0;
      bi = 0;
      while (ai < aSize && bi < bSize) begin
        if (aEdges[ai] == w.bEdges[bi]) return aEdges[ai];
        ai = ai + 1;
        bi = bi + 1;
      end
      return -1;
    endfunction
  endclass
  always_ff @(posedge clk) if (st) begin
    Vertex v;
    Vertex w;
    v = new Vertex();
    w = new Vertex();
    v.aEdges.push_back(1);
    w.bEdges.push_back(1);
    found <= (v.findConnectingEdgep(w) >= 0);
  end
endmodule
module EdgeOpsMod(input logic clk, input logic st, output string nm, output logic cmp);
  class Edge;
    string from;
    string to;
    int weight;
    function new(string f, string t, int w);
      from = f;
      to = t;
      weight = w;
    endfunction
    function string name();
      return {from, "->", to};
    endfunction
    function int sortCmp(ref Edge other);
      if (weight == 0 || other.weight == 0) return 0;
      if (to < other.to) return -1;
      if (to > other.to) return 1;
      return 0;
    endfunction
  endclass
  always_ff @(posedge clk) if (st) begin
    Edge e1;
    Edge e2;
    e1 = new Edge("A", "B", 5);
    e2 = new Edge("A", "C", 0);
    nm  <= e1.name();
    cmp <= (e1.sortCmp(e2) == 0);
  end
endmodule
module GraphClearMod(input logic clk, input logic st, output logic done);
  class Vertex;
    int outE[$];
    function new(); endfunction
  endclass
  class Graph;
    Vertex verts[$];
    function new(); endfunction
    function void clear();
      int i;
      Vertex v;
      for (i = 0; i < verts.size(); i = i + 1) begin
        v = verts[i];
        while (v.outE.size() > 0) v.outE.pop_front();
      end
      while (verts.size() > 0) verts.pop_front();
    endfunction
  endclass
  always_ff @(posedge clk) if (st) begin
    Graph g;
    Vertex v;
    g = new Graph();
    v = new Vertex();
    v.outE.push_back(1);
    g.verts.push_back(v);
    g.clear();
    done <= 1;
  end
endmodule
module UserClearMod(input logic clk, input logic st, output logic done);
  class Vertex;
    int user;
    string userp;
    function new();
      user = 1;
      userp = "";
    endfunction
  endclass
  class Graph;
    Vertex verts[$];
    function new(); endfunction
    function void userClearVertices();
      int i;
      for (i = 0; i < verts.size(); i = i + 1) begin
        verts[i].user  = 0;
        verts[i].userp = "";
      end
    endfunction
    function void userClearEdges();
      int j;
      for (j = 0; j < verts.size(); j = j + 1) begin end
    endfunction
  endclass
  always_ff @(posedge clk) if (st) begin
    Graph g;
    g = new Graph();
    g.verts.push_back(new Vertex());
    g.userClearVertices();
    done <= 1;
  end
endmodule
module ClearColorsMod(input logic clk, input logic st, output logic done);
  class Vertex;
    int color;
    function new(int c);
      color = c;
    endfunction
  endclass
  class Graph;
    Vertex verts[$];
    function new(); endfunction
    function void clearColors();
      int i;
      for (i = 0; i < verts.size(); i = i + 1) begin
        verts[i].color = 0;
      end
    endfunction
  endclass
  always_ff @(posedge clk) if (st) begin
    Graph g;
    g = new Graph();
    g.verts.push_back(new Vertex(3));
    g.clearColors();
    done <= 1;
  end
endmodule
module DumpEdgesMod(input logic clk, input logic st, output int count);
  import "DPI-C" function int fopen(string name, string mode);
  import "DPI-C" function void fwrite(string s, int f);
  import "DPI-C" function void fclose(int f);
  class Vertex;
    string inE[$];
    string outE[$];
    function new(); endfunction
  endclass
  always_ff @(posedge clk) if (st) begin
    int f;
    Vertex v;
    v = new Vertex();
    v.inE.push_back("in");
    v.outE.push_back("out");
    foreach (v.inE[i])  fwrite({"> ", v.inE[i], "\n"}, f);
    foreach (v.outE[j]) fwrite({"-> ", v.outE[j], "\n"}, f);
    fclose(f);
    count <= v.inE.size() + v.outE.size();
  end
endmodule
module DotFileMod(input logic clk, input logic st, output logic done);
  import "DPI-C" function int fopen(string name, string mode);
  import "DPI-C" function void fprintf(int f, string s);
  import "DPI-C" function void fclose(int f);
  class Vertex;
    string name;
    int rank;
    function new(string n, int r);
      name = n;
      rank = r;
    endfunction
    function string dotName();
      return name;
    endfunction
  endclass
  always_ff @(posedge clk) if (st) begin
    int f;
    Vertex verts[$];
    Vertex vA;
    Vertex vB;
    string idx;
    string rnk;
    string line;
    vA = new Vertex("A", 1);
    vB = new Vertex("B", 2);
    verts.push_back(vA);
    verts.push_back(vB);
    f = fopen("dot.dot", "w");
    fprintf(f, "digraph v3graph {\n");
    for (int i = 0; i < verts.size(); i = i + 1) begin
      idx = $sformatf("%0d", i);
      rnk = $sformatf("%0d", verts[i].rank);
      line = {"\tn", verts[i].dotName(), idx, " [label=\"", verts[i].name, " r", rnk, "\"];\n"};
      fprintf(f, line);
    end
    fclose(f);
    done <= 1;
  end
endmodule
