typedef class Vertex_c;
typedef class Graph_c;
class Edge_c;
  local int m_weight;
  local bit m_cutable;
  local int m_userp;
  local Vertex_c m_fromp;
  local Vertex_c m_top;
  function new(Vertex_c fromp_in, Vertex_c top_in, int weight_in, bit cutable_in);
    m_fromp = fromp_in;
    m_top = top_in;
    m_weight = weight_in;
    m_cutable = cutable_in;
    m_userp = 0;
    if (m_fromp != null) m_fromp.add_out_edge(this);
    if (m_top != null) m_top.add_in_edge(this);
  endfunction
  function void relinkFromp(Vertex_c newFromp);
    if (m_fromp != null) m_fromp.remove_out_edge(this);
    m_fromp = newFromp;
    if (m_fromp != null) m_fromp.add_out_edge(this);
  endfunction
  function void relinkTop(Vertex_c newTop);
    if (m_top != null) m_top.remove_in_edge(this);
    m_top = newTop;
    if (m_top != null) m_top.add_in_edge(this);
  endfunction
  function void unlinkDelete();
    if (m_fromp != null) m_fromp.remove_out_edge(this);
    if (m_top != null) m_top.remove_in_edge(this);
  endfunction
  function int get_weight(); return m_weight; endfunction
  function Vertex_c get_fromp(); return m_fromp; endfunction
  function Vertex_c get_top(); return m_top; endfunction
  function bit get_cutable(); return m_cutable; endfunction
  function void set_user(int val); m_userp = val; endfunction
  function int get_user(); return m_userp; endfunction
  function void set_userp(int val); m_userp = val; endfunction
  function int get_userp(); return m_userp; endfunction
  function string get_name();
    string from_name_s = (m_fromp != null) ? m_fromp.get_name() : "null_from";
    string to_name_s = (m_top != null) ? m_top.get_name() : "null_to";
    return {from_name_s, "->", to_name_s};
  endfunction
  function int sortCmp(Edge_c rhsp);
    if (m_weight == 0 || rhsp.m_weight == 0) return 0;
    if (m_weight < rhsp.m_weight) return -1;
    if (m_weight > rhsp.m_weight) return 1;
    return 0;
  endfunction
endclass
class Vertex_c;
  local string m_name;
  local int m_color;
  local int m_rank;
  local real m_fanout;
  local int m_userp;
  Edge_c in_edges[$];
  Edge_c out_edges[$];
  function new(string name_in, bit is_copy = 0, Vertex_c old_vertex = null);
    m_name = name_in;
    if (is_copy && old_vertex != null) begin
      m_fanout = old_vertex.m_fanout;
      m_color = old_vertex.m_color;
      m_rank = old_vertex.m_rank;
      m_userp = 0;
    end else begin
      m_color = 0;
      m_rank = 0;
      m_fanout = 0.0;
      m_userp = 0;
    end
  endfunction
  function void add_in_edge(Edge_c arg_edge);
    in_edges.push_back(arg_edge);
  endfunction
  function void add_out_edge(Edge_c arg_edge);
    out_edges.push_back(arg_edge);
  endfunction
  function void remove_in_edge(Edge_c edge_to_remove);
    for (int i = 0; i < in_edges.size(); i++) begin
      if (in_edges[i] == edge_to_remove) begin
        in_edges.delete(i);
        return;
      end
    end
  endfunction
  function void remove_out_edge(Edge_c edge_to_remove);
    for (int i = 0; i < out_edges.size(); i++) begin
      if (out_edges[i] == edge_to_remove) begin
        out_edges.delete(i);
        return;
      end
    end
  endfunction
  function void unlinkEdges();
    while (out_edges.size() > 0) begin
      automatic Edge_c ep = out_edges.pop_front();
    end
    while (in_edges.size() > 0) begin
      automatic Edge_c ep = in_edges.pop_front();
    end
  endfunction
  function void unlinkDelete(Graph_c graphp);
    unlinkEdges();
    if (graphp != null) graphp.remove_vertex(this);
  endfunction
  function void set_user(int val); m_userp = val; endfunction
  function int get_user(); return m_userp; endfunction
  function void set_userp(int val); m_userp = val; endfunction
  function string get_name(); return m_name; endfunction
  function void set_color(int c); m_color = c; endfunction
  function int get_color(); return m_color; endfunction
  function void set_rank(int r); m_rank = r; endfunction
  function real get_fanout(); return m_fanout; endfunction
  function void set_fanout(real f); m_fanout = f; endfunction
  function void rerouteEdges(Graph_c graphp);
    automatic Edge_c current_in_edges[$];
    automatic Edge_c current_out_edges[$];
    foreach (in_edges[i]) current_in_edges.push_back(in_edges[i]);
    foreach (out_edges[i]) current_out_edges.push_back(out_edges[i]);
    foreach (current_in_edges[i]) begin
      automatic Edge_c iedge = current_in_edges[i];
      foreach (current_out_edges[j]) begin
        automatic Edge_c oedge = current_out_edges[j];
        automatic int new_weight = (iedge.get_weight() < oedge.get_weight()) ? iedge.get_weight() : oedge.get_weight();
        automatic bit new_cutable = iedge.get_cutable() && oedge.get_cutable();
        automatic Edge_c new_edge = new(iedge.get_fromp(), oedge.get_top(), new_weight, new_cutable);
      end
    end
    unlinkEdges();
  endfunction
endclass
class Graph_c;
  local Vertex_c m_vertices[$];
  function new();
  endfunction
  function void destroy();
    clear();
  endfunction
  function void add_vertex(Vertex_c v);
    m_vertices.push_back(v);
  endfunction
  function void remove_vertex(Vertex_c v_to_remove);
    for (int i = 0; i < m_vertices.size(); i++) begin
      if (m_vertices[i] == v_to_remove) begin
        m_vertices.delete(i);
        return;
      end
    end
  endfunction
  function void clear();
    automatic Vertex_c vertices_copy[$];
    foreach (m_vertices[i]) begin
      vertices_copy.push_back(m_vertices[i]);
    end
    foreach (vertices_copy[i]) begin
      automatic Vertex_c v = vertices_copy[i];
      if (v != null) begin
        v.unlinkDelete(this);
      end
    end
    m_vertices.delete();
  endfunction
  function void userClearVertices();
    foreach (m_vertices[i]) begin
      if (m_vertices[i] != null) begin
        m_vertices[i].set_user(0);
        m_vertices[i].set_userp(0);
      end
    end
  endfunction
  function void userClearEdges();
    foreach (m_vertices[i]) begin
      if (m_vertices[i] != null) begin
        foreach (m_vertices[i].out_edges[j]) begin
          if (m_vertices[i].out_edges[j] != null) begin
            m_vertices[i].out_edges[j].set_user(0);
            m_vertices[i].out_edges[j].set_userp(0);
          end
        end
      end
    end
  endfunction
  function void clearColors();
    foreach (m_vertices[i]) begin
      if (m_vertices[i] != null) begin
        m_vertices[i].set_color(0);
      end
    end
  endfunction
endclass
module GraphConstructionAndPropertyOps(
  input bit p_run_init,
  input int p_num_nodes,
  input int p_node_color,
  input int p_node_rank,
  output int p_total_vertices,
  output int p_total_edges,
  output bit p_status_flag
);
  always_comb begin
    automatic Graph_c my_graph;
    automatic Vertex_c v_arr[];
    automatic Edge_c e_arr[];
    automatic int current_vertex_idx;
    automatic int current_edge_idx;
    automatic int actual_num_nodes;
    p_total_vertices = 0;
    p_total_edges = 0;
    p_status_flag = 0;
    current_vertex_idx = 0;
    current_edge_idx = 0;
    if (p_run_init) begin
      my_graph = new();
      actual_num_nodes = p_num_nodes;
      if (actual_num_nodes <= 0) actual_num_nodes = 1;
      v_arr = new[actual_num_nodes];
      if (actual_num_nodes > 1) begin
        e_arr = new[actual_num_nodes * (actual_num_nodes - 1)];
      end else begin
        e_arr = new[0];
      end
      for (int i = 0; i < actual_num_nodes; i++) begin
        automatic string vertex_name;
        $sformat(vertex_name, "V%0d", i);
        if (i % 2 == 0) begin
          v_arr[i] = new(vertex_name);
        end else begin
          automatic Vertex_c old_v_ref;
          old_v_ref = (i > 0) ? v_arr[i-1] : new("DummyOld");
          v_arr[i] = new(vertex_name, 1, old_v_ref);
        end
        my_graph.add_vertex(v_arr[i]);
        current_vertex_idx++;
        v_arr[i].set_color(p_node_color + i);
        v_arr[i].set_rank(p_node_rank + i);
        v_arr[i].set_fanout($urandom_range(100, 1) / 10.0);
        v_arr[i].set_user(i*10);
      end
      for (int i = 0; i < actual_num_nodes; i++) begin
        for (int j = 0; j < actual_num_nodes; j++) begin
          if (i != j && current_edge_idx < e_arr.size()) begin
            if (v_arr[i] != null && v_arr[j] != null) begin
              automatic int weight = $urandom_range(5, 1);
              automatic bit cutable = ($urandom_range(1, 0) == 1);
              e_arr[current_edge_idx] = new(v_arr[i], v_arr[j], weight, cutable);
              e_arr[current_edge_idx].set_user(current_edge_idx*100);
              current_edge_idx++;
            end
          end
        end
      end
      my_graph.userClearVertices();
      my_graph.clearColors();
      my_graph.userClearEdges();
      p_total_vertices = current_vertex_idx;
      p_total_edges = current_edge_idx;
      p_status_flag = 1;
    end
  end
endmodule
module GraphStructureModification(
  input bit p_relink_en,
  input bit p_reroute_en,
  output bit p_relink_status,
  output bit p_reroute_status,
  output int p_edge_sort_result,
  output string p_first_edge_name
);
  always_comb begin
    automatic Graph_c my_graph;
    automatic Vertex_c v_arr[3];
    automatic Edge_c e_arr[3];
    p_relink_status = 0;
    p_reroute_status = 0;
    p_edge_sort_result = 0;
    p_first_edge_name = "";
    my_graph = new();
    v_arr[0] = new("A"); my_graph.add_vertex(v_arr[0]);
    v_arr[1] = new("B"); my_graph.add_vertex(v_arr[1]);
    v_arr[2] = new("C"); my_graph.add_vertex(v_arr[2]);
    e_arr[0] = new(v_arr[0], v_arr[1], 10, 1);
    e_arr[1] = new(v_arr[1], v_arr[2], 20, 0);
    e_arr[2] = new(v_arr[0], v_arr[2], 5, 1);
    if (p_relink_en) begin
      if (e_arr[0] != null && v_arr[2] != null) begin
        e_arr[0].relinkFromp(v_arr[2]);
        p_relink_status = 1;
      end
      if (e_arr[1] != null && v_arr[0] != null) begin
        e_arr[1].relinkTop(v_arr[0]);
        p_relink_status = 1;
      end
    end
    if (p_reroute_en) begin
      if (v_arr[1] != null) begin
        v_arr[1].rerouteEdges(my_graph);
        p_reroute_status = 1;
      end
    end
    if (e_arr[0] != null && e_arr[1] != null) begin
      p_edge_sort_result = e_arr[0].sortCmp(e_arr[1]);
    end
    if (e_arr[0] != null) begin
      p_first_edge_name = e_arr[0].get_name();
    end
  end
endmodule
module GraphDestructionAndCleanup(
  input bit p_clear_en,
  input int p_delete_vertex_idx,
  output bit p_graph_clear_status,
  output bit p_vertex_delete_status
);
  always_comb begin
    automatic Graph_c my_graph;
    automatic Vertex_c initial_vertices[5];
    automatic Edge_c initial_edges[6];
    p_graph_clear_status = 0;
    p_vertex_delete_status = 0;
    my_graph = new();
    for (int i = 0; i < 5; i++) begin
      automatic string v_name;
      $sformat(v_name, "D%0d", i);
      initial_vertices[i] = new(v_name);
      my_graph.add_vertex(initial_vertices[i]);
      initial_vertices[i].set_user(i + 1);
    end
    if (initial_vertices[0] != null && initial_vertices[1] != null) initial_edges[0] = new(initial_vertices[0], initial_vertices[1], 1, 1);
    if (initial_vertices[1] != null && initial_vertices[2] != null) initial_edges[1] = new(initial_vertices[1], initial_vertices[2], 2, 0);
    if (initial_vertices[2] != null && initial_vertices[3] != null) initial_edges[2] = new(initial_vertices[2], initial_vertices[3], 3, 1);
    if (initial_vertices[3] != null && initial_vertices[4] != null) initial_edges[3] = new(initial_vertices[3], initial_vertices[4], 4, 0);
    if (initial_vertices[0] != null && initial_vertices[4] != null) initial_edges[4] = new(initial_vertices[0], initial_vertices[4], 5, 1);
    if (initial_vertices[1] != null && initial_vertices[4] != null) initial_edges[5] = new(initial_vertices[1], initial_vertices[4], 6, 0);
    if (p_delete_vertex_idx >= 0 && p_delete_vertex_idx < 5) begin
      if (initial_vertices[p_delete_vertex_idx] != null) begin
        automatic Vertex_c v_to_delete = initial_vertices[p_delete_vertex_idx];
        v_to_delete.unlinkEdges();
        v_to_delete.unlinkDelete(my_graph);
        initial_vertices[p_delete_vertex_idx] = null;
        p_vertex_delete_status = 1;
      end
    end
    my_graph.userClearEdges();
    if (p_clear_en) begin
      my_graph.clear();
      p_graph_clear_status = 1;
      my_graph.destroy();
    end
  end
endmodule
