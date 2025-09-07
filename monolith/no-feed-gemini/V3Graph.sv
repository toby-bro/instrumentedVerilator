class GraphVertex_SV;
  int        m_fanout;
  int        m_color;
  int        m_rank;
  chandle    m_userp; 
  string     m_name;
  GraphEdge_SV  m_outs_q[$]; 
  GraphEdge_SV  m_ins_q[$];  
  function new(string name_in);
    m_name = name_in;
    m_fanout = 0;
    m_color = 0;
    m_rank = 0;
    m_userp = null; 
  endfunction
  function string name();
    return m_name;
  endfunction
  function void color(int c_val);
    m_color = c_val;
  endfunction
  function int color_get();
    return m_color;
  endfunction
  function void rank(int r_val);
    m_rank = r_val;
  endfunction
  function int rank_get();
    return m_rank;
  endfunction
  function void fanout(int f_val);
    m_fanout = f_val;
  endfunction
  function int fanout_get();
    return m_fanout;
  endfunction
  function void user(int u_val);
    m_userp = u_val;
  endfunction
  function chandle userp_get();
    return m_userp;
  endfunction
  function void userp(chandle u_ptr);
    m_userp = u_ptr;
  endfunction
  function void linkOutEdge(GraphEdge_SV edge_handle);
    m_outs_q.push_back(edge_handle);
    m_fanout = m_outs_q.size(); 
  endfunction
  function void linkInEdge(GraphEdge_SV edge_handle);
    m_ins_q.push_back(edge_handle);
  endfunction
  function void unlinkOutEdge(GraphEdge_SV edge_handle);
    for (int i = 0; i < m_outs_q.size(); i++) begin
      if (m_outs_q[i] == edge_handle) begin
        m_outs_q.delete(i);
        break;
      end
    end
    m_fanout = m_outs_q.size();
  endfunction
  function void unlinkInEdge(GraphEdge_SV edge_handle);
    for (int i = 0; i < m_ins_q.size(); i++) begin
      if (m_ins_q[i] == edge_handle) begin
        m_ins_q.delete(i);
        break;
      end
    end
  endfunction
  function GraphEdge_SV unlinkFrontOutEdge();
    if (m_outs_q.size() > 0) begin
      GraphEdge_SV temp_edge = m_outs_q.pop_front();
      m_fanout = m_outs_q.size();
      return temp_edge;
    end
    return null;
  endfunction
  function GraphEdge_SV unlinkFrontInEdge();
    if (m_ins_q.size() > 0) begin
      return m_ins_q.pop_front();
    end
    return null;
  endfunction
  function void unlinkEdges();
    while (m_outs_q.size() > 0) begin
      GraphEdge_SV ep = m_outs_q.pop_front();
      if (ep != null) begin
        ep.unlinkToVertex(); 
        ep = null; 
      end
    end
    while (m_ins_q.size() > 0) begin
      GraphEdge_SV ep = m_ins_q.pop_front();
      if (ep != null) begin
        ep.unlinkFromVertex(); 
        ep = null; 
      end
    end
  endfunction
  function void unlinkDelete();
    this.unlinkEdges(); 
  endfunction
  function void rerouteEdges(Graph_SV graph_handle);
    foreach (m_ins_q[i]) begin
      foreach (m_outs_q[j]) begin
        GraphVertex_SV new_from_v = m_ins_q[i].get_from();
        GraphVertex_SV new_to_v = m_outs_q[j].get_to();
        int new_weight = (m_ins_q[i].get_weight() < m_outs_q[j].get_weight()) ? m_ins_q[i].get_weight() : m_outs_q[j].get_weight();
        logic new_cutable = m_ins_q[i].get_cutable() && m_outs_q[j].get_cutable();
        void'(new GraphEdge_SV(graph_handle, new_from_v, new_to_v, new_weight, new_cutable));
      end
    end
    this.unlinkEdges();
  endfunction
  function GraphEdge_SV findConnectingEdge(GraphVertex_SV waywardp_in);
    foreach (m_outs_q[i]) begin
      if (m_outs_q[i].get_to() == waywardp_in) return m_outs_q[i];
    end
    foreach (m_ins_q[i]) begin
      if (m_ins_q[i].get_from() == waywardp_in) return m_ins_q[i];
    end
    return null;
  endfunction
endclass
class GraphEdge_SV;
  GraphVertex_SV m_fromp;
  GraphVertex_SV m_top;
  int            m_weight;
  logic          m_cutable;
  chandle        m_userp;
  function new(Graph_SV graph_handle, GraphVertex_SV fromp_in, GraphVertex_SV top_in, int weight_in, logic cutable_in);
    m_fromp = fromp_in;
    m_top = top_in;
    m_weight = weight_in;
    m_cutable = cutable_in;
    m_userp = null;
    m_fromp.linkOutEdge(this);
    m_top.linkInEdge(this);
  endfunction
  function string name();
    if (m_fromp != null && m_top != null)
      return {m_fromp.name(), "->", m_top.name()};
    else return "null->null";
  endfunction
  function GraphVertex_SV get_from();
    return m_fromp;
  endfunction
  function GraphVertex_SV get_to();
    return m_top;
  endfunction
  function int get_weight();
    return m_weight;
  endfunction
  function logic get_cutable();
    return m_cutable;
  endfunction
  function void user(int u_val);
    m_userp = u_val;
  endfunction
  function chandle userp_get();
    return m_userp;
  endfunction
  function void userp(chandle u_ptr);
    m_userp = u_ptr;
  endfunction
  function void relinkFromp(GraphVertex_SV newFromp);
    m_fromp.unlinkOutEdge(this); 
    m_fromp = newFromp;         
    m_fromp.linkOutEdge(this);  
  endfunction
  function void relinkTop(GraphVertex_SV newTop);
    m_top.unlinkInEdge(this); 
    m_top = newTop;           
    m_top.linkInEdge(this);   
  endfunction
  function void unlinkDelete();
    this.unlinkFromVertex();
    this.unlinkToVertex();
  endfunction
  function void unlinkFromVertex();
    if (m_fromp != null) m_fromp.unlinkOutEdge(this);
  endfunction
  function void unlinkToVertex();
    if (m_top != null) m_top.unlinkInEdge(this);
  endfunction
  function int sortCmp(GraphEdge_SV rhsp);
    if (m_weight == 0 || rhsp.m_weight == 0) return 0; 
    if (m_weight < rhsp.m_weight) return -1;
    if (m_weight > rhsp.m_weight) return 1;
    return 0;
  endfunction
endclass
class Graph_SV;
  GraphVertex_SV m_vertices_q[$]; 
  function new();
  endfunction
  function GraphVertex_SV createVertex(string name_in);
    GraphVertex_SV new_v = new GraphVertex_SV(name_in);
    m_vertices_q.push_back(new_v); 
    return new_v;
  endfunction
  function GraphVertex_SV createVertexCopy(GraphVertex_SV old_vertex, string name_suffix);
    GraphVertex_SV new_v = new GraphVertex_SV({old_vertex.m_name, name_suffix});
    new_v.m_fanout = old_vertex.m_fanout;
    new_v.m_color = old_vertex.m_color;
    new_v.m_rank = old_vertex.m_rank;
    new_v.m_userp = null; 
    m_vertices_q.push_back(new_v); 
    return new_v;
  endfunction
  function void clear();
    foreach (m_vertices_q[i]) begin
      while (m_vertices_q[i].m_outs_q.size() > 0) begin
        GraphEdge_SV edgep = m_vertices_q[i].unlinkFrontOutEdge();
        if (edgep != null) begin
          edgep.unlinkToVertex(); 
        end
      end
    end
    while (m_vertices_q.size() > 0) begin
      GraphVertex_SV vertexp = m_vertices_q.pop_front();
    end
  endfunction
  function void userClearVertices();
    foreach (m_vertices_q[i]) begin
      m_vertices_q[i].user(0);
      m_vertices_q[i].userp(null);
    end
  endfunction
  function void userClearEdges();
    foreach (m_vertices_q[i]) begin
      foreach (m_vertices_q[i].m_outs_q[j]) begin
        m_vertices_q[i].m_outs_q[j].user(0);
        m_vertices_q[i].m_outs_q[j].userp(null);
      end
    end
  endfunction
  function void clearColors();
    foreach (m_vertices_q[i]) begin
      m_vertices_q[i].color(0);
    end
  endfunction
  function void dump_graph();
    foreach (m_vertices_q[i]) begin
      void'(m_vertices_q[i].name());
      void'(m_vertices_q[i].color_get());
      void'(m_vertices_q[i].rank_get());
      void'(m_vertices_q[i].fanout_get());
      foreach (m_vertices_q[i].m_ins_q[k]) begin
        void'(m_vertices_q[i].m_ins_q[k].get_weight());
        void'(m_vertices_q[i].m_ins_q[k].get_from());
        void'(m_vertices_q[i].m_ins_q[k].get_to());
        void'(m_vertices_q[i].m_ins_q[k].get_cutable());
      end
      foreach (m_vertices_q[i].m_outs_q[k]) begin
        void'(m_vertices_q[i].m_outs_q[k].get_weight());
        void'(m_vertices_q[i].m_outs_q[k].get_from());
        void'(m_vertices_q[i].m_outs_q[k].get_to());
        void'(m_vertices_q[i].m_outs_q[k].get_cutable());
      end
    end
  endfunction
  function GraphVertex_SV getVertex(int index);
    if (index >= 0 && index < m_vertices_q.size()) return m_vertices_q[index];
    return null;
  endfunction
endclass
module GraphBasicOps (
  input logic [7:0] in_node_count, 
  output int        out_final_vertex_count,
  output int        out_final_edge_count
);
  Graph_SV my_graph_m1;
  GraphVertex_SV vertices_local[256]; 
  always_comb begin
    my_graph_m1 = new(); 
    out_final_vertex_count = 0;
    out_final_edge_count = 0;
    for (int i = 0; i < in_node_count; i++) begin
      string vertex_name = {"v", $sformatf("%0d", i)};
      vertices_local[i] = my_graph_m1.createVertex(vertex_name);
      out_final_vertex_count++;
    end
    for (int i = 0; i < in_node_count - 1; i++) begin
      if (vertices_local[i] != null && vertices_local[i+1] != null) begin
        void'(new GraphEdge_SV(my_graph_m1, vertices_local[i], vertices_local[i+1], 10 + i, 1));
        out_final_edge_count++;
      end
    end
    if (out_final_edge_count > 0 && my_graph_m1.getVertex(0) != null && my_graph_m1.getVertex(0).m_outs_q.size() > 0) begin
      GraphEdge_SV edge_to_delete = my_graph_m1.getVertex(0).m_outs_q.pop_front();
      if (edge_to_delete != null) begin
        edge_to_delete.unlinkDelete();
        edge_to_delete = null;
      end
    end
    if (out_final_vertex_count > 0) begin
      GraphVertex_SV vertex_to_delete = my_graph_m1.getVertex(in_node_count / 2); 
      if (vertex_to_delete != null) begin
        for (int i = 0; i < my_graph_m1.m_vertices_q.size(); i++) begin
          if (my_graph_m1.m_vertices_q[i] == vertex_to_delete) begin
            my_graph_m1.m_vertices_q.delete(i);
            break;
          end
        end
        vertex_to_delete.unlinkDelete(); 
        vertex_to_delete = null;
      end
    end
    if (in_node_count > 5) begin 
      my_graph_m1.clear();
      out_final_vertex_count = 0;
      out_final_edge_count = 0;
    end
    my_graph_m1 = null; 
  end
endmodule
module GraphEdgeManipulation (
  input logic in_trigger_relink,
  input int   in_edge_weight_a,
  output int  out_sort_cmp_result,
  output int  out_cleared_edge_users_count
);
  Graph_SV my_graph_m2;
  GraphVertex_SV vA_m2, vB_m2, vC_m2, vD_m2;
  GraphEdge_SV e1_m2, e2_m2;
  always_comb begin
    out_sort_cmp_result = 0;
    out_cleared_edge_users_count = 0;
    my_graph_m2 = new();
    vA_m2 = my_graph_m2.createVertex("VertA");
    vB_m2 = my_graph_m2.createVertex("VertB");
    vC_m2 = my_graph_m2.createVertex("VertC");
    vD_m2 = my_graph_m2.createVertex("VertD");
    e1_m2 = new GraphEdge_SV(my_graph_m2, vA_m2, vB_m2, in_edge_weight_a, 1);
    e2_m2 = new GraphEdge_SV(my_graph_m2, vB_m2, vC_m2, 20, 0);
    e1_m2.user(101);
    e2_m2.userp(202);
    void'(e1_m2.name());
    if (in_trigger_relink) begin
      e1_m2.relinkFromp(vD_m2); 
      e2_m2.relinkTop(vA_m2); 
      out_sort_cmp_result = e1_m2.sortCmp(e2_m2);
      my_graph_m2.userClearEdges();
      if (e1_m2.userp_get() == null && e2_m2.userp_get() == null) begin
        out_cleared_edge_users_count = 1;
      end
    end
    my_graph_m2.clear();
    my_graph_m2 = null;
  end
endmodule
module GraphVertexProperties (
  input logic in_reset_properties,
  input int   in_base_color,
  output int  out_total_color,
  output int  out_total_rank,
  output int  out_cleared_vertex_users
);
  Graph_SV my_graph_m3;
  GraphVertex_SV v_prop[5];
  always_comb begin
    out_total_color = 0;
    out_total_rank = 0;
    out_cleared_vertex_users = 0;
    my_graph_m3 = new();
    for (int i = 0; i < 5; i++) begin
      v_prop[i] = my_graph_m3.createVertex({$sformatf("PropV%0d", i)});
      v_prop[i].color(in_base_color + i); 
      v_prop[i].rank(i * 2);             
      v_prop[i].user(i + 100);           
      out_total_color += v_prop[i].color_get();
      out_total_rank += v_prop[i].rank_get();
      if (i < 4) begin
        void'(new GraphEdge_SV(my_graph_m3, v_prop[i], v_prop[i+1], 1, 1));
      end
    end
    if (in_reset_properties) begin
      my_graph_m3.userClearVertices();
      out_cleared_vertex_users = 1; 
      my_graph_m3.clearColors();
      out_total_color = 0; 
      foreach (v_prop[i]) begin
          out_total_color += v_prop[i].color_get(); 
      end
    end
    my_graph_m3.dump_graph(); 
    my_graph_m3.clear();
    my_graph_m3 = null;
  end
endmodule
module GraphAdvancedOperations (
  input logic in_trigger_advanced,
  input int   in_edge_src_weight,
  output int  out_rerouted_potential_edges,
  output int  out_found_edge_final_weight
);
  Graph_SV my_graph_m4;
  GraphVertex_SV adv_v[4];
  GraphEdge_SV adv_e[5];
  always_comb begin
    out_rerouted_potential_edges = 0;
    out_found_edge_final_weight = 0;
    my_graph_m4 = new();
    adv_v[0] = my_graph_m4.createVertex("Source");
    adv_v[1] = my_graph_m4.createVertex("Middle1");
    adv_v[2] = my_graph_m4.createVertex("Middle2");
    adv_v[3] = my_graph_m4.createVertex("Sink");
    adv_e[0] = new GraphEdge_SV(my_graph_m4, adv_v[0], adv_v[1], in_edge_src_weight, 1);
    adv_e[1] = new GraphEdge_SV(my_graph_m4, adv_v[1], adv_v[3], 20, 1);
    adv_e[2] = new GraphEdge_SV(my_graph_m4, adv_v[0], adv_v[2], 30, 0);
    adv_e[3] = new GraphEdge_SV(my_graph_m4, adv_v[2], adv_v[3], 40, 0);
    adv_e[4] = new GraphEdge_SV(my_graph_m4, adv_v[1], adv_v[2], 55, 1); 
    if (in_trigger_advanced) begin
      if (adv_v[1] != null) begin
          int initial_in_edges = adv_v[1].m_ins_q.size();
          int initial_out_edges = adv_v[1].m_outs_q.size();
          adv_v[1].rerouteEdges(my_graph_m4);
          out_rerouted_potential_edges = initial_in_edges * initial_out_edges;
      end
      GraphEdge_SV found_edge = adv_v[1].findConnectingEdge(adv_v[2]); 
      if (found_edge != null) begin
        out_found_edge_final_weight = found_edge.get_weight();
      end
    end
    my_graph_m4.clear();
    my_graph_m4 = null;
  end
endmodule
module GraphCopyConstructor (
  input logic in_perform_copy,
  output int  out_copied_vertex_color_val
);
  Graph_SV my_graph_m5;
  GraphVertex_SV original_v_m5;
  GraphVertex_SV copied_v_m5;
  always_comb begin
    out_copied_vertex_color_val = 0;
    my_graph_m5 = new();
    original_v_m5 = my_graph_m5.createVertex("original_vertex");
    original_v_m5.color(123);
    original_v_m5.rank(10);
    original_v_m5.fanout(5);
    original_v_m5.user(99);
    if (in_perform_copy) begin
      copied_v_m5 = my_graph_m5.createVertexCopy(original_v_m5, "_Cpy");
      out_copied_vertex_color_val = copied_v_m5.color_get();
      void'(copied_v_m5.rank_get());
      void'(copied_v_m5.fanout_get());
      void'(copied_v_m5.userp_get());
    end
    my_graph_m5.clear();
    my_graph_m5 = null;
  end
endmodule
