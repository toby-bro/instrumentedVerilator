typedef class GraphVertex_SV;
typedef class GraphEdge_SV;
typedef class Graph_SV;
class GraphVertex_SV;
  GraphVertex_SV m_next_vertex;
  GraphVertex_SV m_prev_vertex;
  GraphEdge_SV m_out_edges_head;
  GraphEdge_SV m_out_edges_tail;
  GraphEdge_SV m_in_edges_head;
  GraphEdge_SV m_in_edges_tail;
  int m_fanout;
  int m_color;
  int m_rank;
  string m_name;
  int m_user_int;
  int m_out_edge_count; 
  int m_in_edge_count;  
  function new(string name_p, int init_color, int init_rank);
    m_name = name_p;
    m_fanout = 0;
    m_color = init_color;
    m_rank = init_rank;
    m_user_int = 0;
    m_next_vertex = null;
    m_prev_vertex = null;
    m_out_edges_head = null;
    m_out_edges_tail = null;
    m_in_edges_head = null;
    m_in_edges_tail = null;
    m_out_edge_count = 0;
    m_in_edge_count = 0;
  endfunction
  function void add_out_edge(GraphEdge_SV edge_p);
    if (m_out_edges_head == null) begin
      m_out_edges_head = edge_p;
      m_out_edges_tail = edge_p;
    end else begin
      m_out_edges_tail.m_next_edge = edge_p;
      edge_p.m_prev_edge = m_out_edges_tail;
      m_out_edges_tail = edge_p;
    end
    m_out_edge_count++;
  endfunction
  function void add_in_edge(GraphEdge_SV edge_p);
    if (m_in_edges_head == null) begin
      m_in_edges_head = edge_p;
      m_in_edges_tail = edge_p;
    end else begin
      m_in_edges_tail.m_next_edge = edge_p;
      edge_p.m_prev_edge = m_in_edges_tail;
      m_in_edges_tail = edge_p;
    end
    m_in_edge_count++;
  endfunction
  function void remove_out_edge(GraphEdge_SV edge_p);
    if (edge_p.m_prev_edge != null) edge_p.m_prev_edge.m_next_edge = edge_p.m_next_edge;
    if (edge_p.m_next_edge != null) edge_p.m_next_edge.m_prev_edge = edge_p.m_prev_edge;
    if (m_out_edges_head == edge_p) m_out_edges_head = edge_p.m_next_edge;
    if (m_out_edges_tail == edge_p) m_out_edges_tail = edge_p.m_prev_edge;
    edge_p.m_next_edge = null;
    edge_p.m_prev_edge = null;
    m_out_edge_count--;
  endfunction
  function void remove_in_edge(GraphEdge_SV edge_p);
    if (edge_p.m_prev_edge != null) edge_p.m_prev_edge.m_next_edge = edge_p.m_next_edge;
    if (edge_p.m_next_edge != null) edge_p.m_next_edge.m_prev_edge = edge_p.m_prev_edge;
    if (m_in_edges_head == edge_p) m_in_edges_head = edge_p.m_next_edge;
    if (m_in_edges_tail == edge_p) m_in_edges_tail = edge_p.m_prev_edge;
    edge_p.m_next_edge = null;
    edge_p.m_prev_edge = null;
    m_in_edge_count--;
  endfunction
  function void unlinkEdges_sv();
    m_out_edges_head = null;
    m_out_edges_tail = null;
    m_in_edges_head = null;
    m_in_edges_tail = null;
    m_out_edge_count = 0;
    m_in_edge_count = 0;
  endfunction
  function void unlinkDelete_sv();
    unlinkEdges_sv();
    m_name = "DELETED_VERTEX";
    m_fanout = -1;
    m_color = -1;
    m_rank = -1;
    m_user_int = -1;
    m_next_vertex = null;
    m_prev_vertex = null;
  endfunction
  function void rerouteEdges_sv(Graph_SV graph_handle);
    GraphEdge_SV temp_new_edges_head = null;
    GraphEdge_SV temp_new_edges_tail = null;
    GraphEdge_SV current_in_edge = m_in_edges_head;
    while (current_in_edge != null) begin
      GraphEdge_SV current_out_edge = m_out_edges_head;
      while (current_out_edge != null) begin
        int new_weight = (current_in_edge.m_weight < current_out_edge.m_weight) ? current_in_edge.m_weight : current_out_edge.m_weight;
        bit new_cutable = current_in_edge.m_cutable && current_out_edge.m_cutable;
        GraphEdge_SV new_edge = new(current_in_edge.m_fromp, current_out_edge.m_top, new_weight, new_cutable);
        if (temp_new_edges_head == null) begin
          temp_new_edges_head = new_edge;
          temp_new_edges_tail = new_edge;
        end else begin
          temp_new_edges_tail.m_next_edge = new_edge;
          new_edge.m_prev_edge = temp_new_edges_tail;
          temp_new_edges_tail = new_edge;
        end
        current_out_edge = current_out_edge.m_next_edge;
      end
      current_in_edge = current_in_edge.m_next_edge;
    end
    GraphEdge_SV add_edge_ptr = temp_new_edges_head;
    while (add_edge_ptr != null) begin
      GraphEdge_SV next_ptr = add_edge_ptr.m_next_edge;
      add_edge_ptr.m_next_edge = null;
      add_edge_ptr.m_prev_edge = null;
      graph_handle.add_edge(add_edge_ptr);
      add_edge_ptr = next_ptr;
    end
    unlinkEdges_sv();
  endfunction
  function GraphEdge_SV findConnectingEdgep_sv(GraphVertex_SV waywardp);
    GraphEdge_SV current_edge;
    current_edge = m_out_edges_head;
    while (current_edge != null) begin
      if (current_edge.m_top == waywardp) return current_edge;
      current_edge = current_edge.m_next_edge;
    }
    current_edge = m_in_edges_head;
    while (current_edge != null) begin
      if (current_edge.m_fromp == waywardp) return current_edge;
      current_edge = current_edge.m_next_edge;
    }
    return null;
  endfunction
  function void trigger_v3error_sv(string message, bit is_fatal);
    if (is_fatal) begin
      $fatal(1, "V3GraphVertex Fatal Error (simulated): %0s for vertex %0s", message, m_name);
    end else begin
      $error("V3GraphVertex Error (simulated): %0s for vertex %0s", message, m_name);
    end
  endfunction
  function string get_formatted_info();
    string info_str;
    info_str = $sformatf("VERTEX=%0s", m_name);
    if (m_rank != 0) info_str = $sformatf("%0s r%0d", info_str, m_rank);
    if (m_fanout != 0) info_str = $sformatf("%0s f%0d", info_str, m_fanout);
    if (m_color != 0) info_str = $sformatf("%0s c%0d", info_str, m_color);
    return info_str;
  endfunction
  function void set_user_int(int val); m_user_int = val; endfunction
  function int get_user_int(); return m_user_int; endfunction
  function void set_color(int val); m_color = val; endfunction
  function int get_color(); return m_color; endfunction
  function string get_name(); return m_name; endfunction
  function void set_fanout(int val); m_fanout = val; endfunction
  function int get_rank(); return m_rank; endfunction
endclass
class GraphEdge_SV;
  GraphEdge_SV m_next_edge;
  GraphEdge_SV m_prev_edge;
  GraphVertex_SV m_fromp;
  GraphVertex_SV m_top;
  int m_weight;
  bit m_cutable;
  int m_user_int;
  function new(GraphVertex_SV fromp_in, GraphVertex_SV top_in, int weight_in, bit cutable_in);
    if (fromp_in == null || top_in == null) begin
      $fatal(1, "GraphEdge_SV: Null 'from' or 'to' vertex pointer provided.");
    end
    m_fromp = fromp_in;
    m_top = top_in;
    m_weight = weight_in;
    m_cutable = cutable_in;
    m_user_int = 0;
    m_next_edge = null;
    m_prev_edge = null;
    m_fromp.add_out_edge(this);
    m_top.add_in_edge(this);
  endfunction
  function void relinkFromp_sv(GraphVertex_SV newFromp);
    if (newFromp == null) begin
      $fatal(1, "GraphEdge_SV: Null 'newFromp' for relinkFromp_sv.");
    end
    m_fromp.remove_out_edge(this);
    m_fromp = newFromp;
    m_fromp.add_out_edge(this);
  endfunction
  function void relinkTop_sv(GraphVertex_SV newTop);
    if (newTop == null) begin
      $fatal(1, "GraphEdge_SV: Null 'newTop' for relinkTop_sv.");
    end
    m_top.remove_in_edge(this);
    m_top = newTop;
    m_top.add_in_edge(this);
  endfunction
  function void unlinkDelete_sv();
    m_fromp.remove_out_edge(this);
    m_top.remove_in_edge(this);
    m_fromp = null;
    m_top = null;
    m_weight = -1;
    m_cutable = 0;
    m_user_int = -1;
    m_next_edge = null;
    m_prev_edge = null;
  endfunction
  function string get_name();
    if (m_fromp != null && m_top != null) begin
      return $sformatf("%0s->%0s", m_fromp.get_name(), m_top.get_name());
    end else begin
      return "NULL_EDGE";
    end
  endfunction
  function int sortCmp_sv(GraphEdge_SV rhsp);
    if (m_weight == 0 || rhsp.m_weight == 0) return 0;
    if (m_weight < rhsp.m_weight) return -1;
    else if (m_weight > rhsp.m_weight) return 1;
    else return 0;
  endfunction
  function void set_user_int(int val); m_user_int = val; endfunction
  function int get_user_int(); return m_user_int; endfunction
  function int get_weight(); return m_weight; endfunction
  function bit get_cutable(); return m_cutable; endfunction
endclass
class Graph_SV;
  GraphVertex_SV m_vertices_head;
  GraphVertex_SV m_vertices_tail;
  int m_vertex_count;
  GraphEdge_SV m_edges_head;
  GraphEdge_SV m_edges_tail;
  int m_edge_count;
  function new();
    m_vertices_head = null;
    m_vertices_tail = null;
    m_vertex_count = 0;
    m_edges_head = null;
    m_edges_tail = null;
    m_edge_count = 0;
  endfunction
  function void clear_sv();
    GraphEdge_SV current_edge = m_edges_head;
    while (current_edge != null) begin
      GraphEdge_SV next_edge = current_edge.m_next_edge;
      current_edge.unlinkDelete_sv();
      current_edge = next_edge;
    end
    m_edges_head = null;
    m_edges_tail = null;
    m_edge_count = 0;
    GraphVertex_SV current_vertex = m_vertices_head;
    while (current_vertex != null) begin
      GraphVertex_SV next_vertex = current_vertex.m_next_vertex;
      current_vertex.unlinkDelete_sv();
      current_vertex = next_vertex;
    end
    m_vertices_head = null;
    m_vertices_tail = null;
    m_vertex_count = 0;
  endfunction
  function void add_vertex(GraphVertex_SV v_in);
    if (m_vertices_head == null) begin
      m_vertices_head = v_in;
      m_vertices_tail = v_in;
    end else begin
      m_vertices_tail.m_next_vertex = v_in;
      v_in.m_prev_vertex = m_vertices_tail;
      m_vertices_tail = v_in;
    end
    m_vertex_count++;
  endfunction
  function GraphVertex_SV pop_back_vertex();
    GraphVertex_SV popped_vertex = null;
    if (m_vertices_tail != null) begin
      popped_vertex = m_vertices_tail;
      if (m_vertices_tail.m_prev_vertex != null) begin
        m_vertices_tail.m_prev_vertex.m_next_vertex = null;
        m_vertices_tail = m_vertices_tail.m_prev_vertex;
      end else begin
        m_vertices_head = null;
        m_vertices_tail = null;
      end
      popped_vertex.m_next_vertex = null;
      popped_vertex.m_prev_vertex = null;
      m_vertex_count--;
    end
    return popped_vertex;
  endfunction
  function void remove_vertex(GraphVertex_SV v_in);
    if (v_in.m_prev_vertex != null) v_in.m_prev_vertex.m_next_vertex = v_in.m_next_vertex;
    if (v_in.m_next_vertex != null) v_in.m_next_vertex.m_prev_vertex = v_in.m_prev_vertex;
    if (m_vertices_head == v_in) m_vertices_head = v_in.m_next_vertex;
    if (m_vertices_tail == v_in) m_vertices_tail = v_in.m_prev_vertex;
    v_in.m_next_vertex = null;
    v_in.m_prev_vertex = null;
    m_vertex_count--;
  endfunction
  function void add_edge(GraphEdge_SV e_in);
    if (m_edges_head == null) begin
      m_edges_head = e_in;
      m_edges_tail = e_in;
    end else begin
      m_edges_tail.m_next_edge = e_in;
      e_in.m_prev_edge = m_edges_tail;
      m_edges_tail = e_in;
    end
    m_edge_count++;
  endfunction
  function void remove_edge(GraphEdge_SV e_in);
    if (e_in.m_prev_edge != null) e_in.m_prev_edge.m_next_edge = e_in.m_next_edge;
    if (e_in.m_next_edge != null) e_in.m_next_edge.m_prev_edge = e_in.m_prev_edge;
    if (m_edges_head == e_in) m_edges_head = e_in.m_next_edge;
    if (m_edges_tail == e_in) m_edges_tail = e_in.m_prev_edge;
    e_in.m_next_edge = null;
    e_in.m_prev_edge = null;
    m_edge_count--;
  endfunction
  function void userClearVertices_sv();
    GraphVertex_SV current_vertex = m_vertices_head;
    while (current_vertex != null) begin
      current_vertex.set_user_int(0);
      current_vertex = current_vertex.m_next_vertex;
    end
  endfunction
  function void userClearEdges_sv();
    GraphEdge_SV current_edge = m_edges_head;
    while (current_edge != null) begin
      current_edge.set_user_int(0);
      current_edge = current_edge.m_next_edge;
    end
  endfunction
  function void clearColors_sv();
    GraphVertex_SV current_vertex = m_vertices_head;
    while (current_vertex != null) begin
      current_vertex.set_color(0);
      current_vertex = current_vertex.m_next_vertex;
    end
  endfunction
  function string reportLoops_sv(GraphVertex_SV loop_vertex);
    string report_str;
    if (loop_vertex != null) begin
      report_str = $sformatf("-Info-Loop: %0s %0s\n", loop_vertex.get_name(), loop_vertex.get_formatted_info());
    end else begin
      report_str = "";
    end
    report_str = $sformatf("%0sLoops detected in graph (simulated)", report_str);
    return report_str;
  endfunction
  function void dump_graph_sv(string comment, bit color_as_subgraph);
    $display("--- SIMULATED GRAPH DUMP: %0s (colorAsSubgraph=%0b) ---", comment, color_as_subgraph);
    $display("Graph Vertex Count: %0d", m_vertex_count);
    GraphVertex_SV current_vertex = m_vertices_head;
    while (current_vertex != null) begin
      $display("  Node: %0s (Color: %0d, Rank: %0d, Fanout: %0d)",
               current_vertex.get_name(), current_vertex.get_color(), current_vertex.get_rank(), current_vertex.m_fanout);
      GraphEdge_SV current_out_edge = current_vertex.m_out_edges_head;
      while (current_out_edge != null) begin
        if (current_out_edge.get_weight() != 0 && current_out_edge.m_fromp == current_vertex) begin
          string edge_info_str;
          edge_info_str = $sformatf("\t\t-> %0s", current_out_edge.m_top.get_name());
          if (current_out_edge.get_cutable()) edge_info_str = $sformatf("%0s  [CUTABLE]", edge_info_str);
          $display("%0s", edge_info_str);
        end
        current_out_edge = current_out_edge.m_next_edge;
      end
      GraphEdge_SV current_in_edge = current_vertex.m_in_edges_head;
      while (current_in_edge != null) begin
        if (current_in_edge.get_weight() != 0 && current_in_edge.m_top == current_vertex) begin
          string edge_info_str;
          edge_info_str = $sformatf("\t\t<- %0s", current_in_edge.m_fromp.get_name());
          if (current_in_edge.get_cutable()) edge_info_str = $sformatf("%0s  [CUTABLE]", edge_info_str);
          $display("%0s", edge_info_str);
        end
        current_in_edge = current_in_edge.m_next_edge;
      end
      current_vertex = current_vertex.m_next_vertex;
    end
    $display("Graph Edge Count: %0d", m_edge_count);
    GraphEdge_SV current_global_edge = m_edges_head;
    while (current_global_edge != null) begin
        if (current_global_edge.get_weight() != 0) begin
            $display("  Edge %0s (Weight: %0d, Cutable: %0b)", current_global_edge.get_name(), current_global_edge.get_weight(), current_global_edge.get_cutable());
        end
        current_global_edge = current_global_edge.m_next_edge;
    end
    $display("--- END SIMULATED GRAPH DUMP ---");
  endfunction
  function int get_vertex_count(); return m_vertex_count; endfunction
  function int get_edge_count(); return m_edge_count; endfunction
endclass
module VertexGraphOps (
  input logic clk,
  input logic rst_n,
  input logic add_vertex_cmd,
  input logic delete_vertex_cmd,
  input int   num_vertices_to_add,
  output int  current_vertex_count_out
);
  Graph_SV my_graph;
  int vertex_name_counter;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      my_graph = new();
      vertex_name_counter = 0;
      current_vertex_count_out <= 0;
    end else begin
      if (add_vertex_cmd) begin
        for (int i = 0; i < num_vertices_to_add; i++) begin
          string v_name = $sformatf("V%0d", vertex_name_counter);
          GraphVertex_SV new_v = new(v_name, vertex_name_counter % 3, vertex_name_counter / 2);
          new_v.set_fanout(vertex_name_counter * 10);
          my_graph.add_vertex(new_v);
          vertex_name_counter++;
        end
      end
      if (delete_vertex_cmd && my_graph.m_vertex_count > 0) begin
        GraphVertex_SV v_to_delete = my_graph.pop_back_vertex();
        if (v_to_delete != null) begin
          v_to_delete.unlinkDelete_sv();
        end
      end
      current_vertex_count_out <= my_graph.get_vertex_count();
    end
  end
endmodule
module EdgeGraphOps (
  input logic clk,
  input logic rst_n,
  input logic add_edge_cmd,
  input logic relink_edge_cmd,
  input logic delete_edge_cmd,
  output int  current_edge_count_out,
  output int  sort_cmp_result_out
);
  Graph_SV my_graph;
  GraphVertex_SV v_a, v_b, v_c, v_d;
  GraphEdge_SV e_ab, e_bc, e_cd, e_ac;
  int edge_op_state;
  localparam S_IDLE = 0;
  localparam S_INIT_VERTS = 1;
  localparam S_ADD_EDGES = 2;
  localparam S_RELINK_EDGE_FROM = 3;
  localparam S_RELINK_EDGE_TO = 4;
  localparam S_SORT_CMP = 5;
  localparam S_DELETE_EDGE = 6;
  localparam S_DONE = 7;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      my_graph = new();
      v_a = null; v_b = null; v_c = null; v_d = null;
      e_ab = null; e_bc = null; e_cd = null; e_ac = null;
      edge_op_state <= S_IDLE;
      current_edge_count_out <= 0;
      sort_cmp_result_out <= 0;
    end else begin
      case (edge_op_state)
        S_IDLE: begin
          if (add_edge_cmd) edge_op_state <= S_INIT_VERTS;
        end
        S_INIT_VERTS: begin
          v_a = new("VA", 0, 0); my_graph.add_vertex(v_a);
          v_b = new("VB", 1, 1); my_graph.add_vertex(v_b);
          v_c = new("VC", 2, 2); my_graph.add_vertex(v_c);
          v_d = new("VD", 3, 3); my_graph.add_vertex(v_d);
          edge_op_state <= S_ADD_EDGES;
        end
        S_ADD_EDGES: begin
          e_ab = new(v_a, v_b, 10, 1'b1); my_graph.add_edge(e_ab);
          e_bc = new(v_b, v_c, 5, 1'b0);  my_graph.add_edge(e_bc);
          e_cd = new(v_c, v_d, 20, 1'b1); my_graph.add_edge(e_cd);
          e_ac = new(v_a, v_c, 0, 1'b0);  my_graph.add_edge(e_ac);
          edge_op_state <= S_RELINK_EDGE_FROM;
        end
        S_RELINK_EDGE_FROM: begin
          if (relink_edge_cmd && e_ab != null) begin
            e_ab.relinkFromp_sv(v_c);
            edge_op_state <= S_RELINK_EDGE_TO;
          end else if (!relink_edge_cmd) begin
            edge_op_state <= S_SORT_CMP;
          end
        end
        S_RELINK_EDGE_TO: begin
          if (relink_edge_cmd && e_bc != null) begin
            e_bc.relinkTop_sv(v_a);
            edge_op_state <= S_SORT_CMP;
          end else if (!relink_edge_cmd) begin
            edge_op_state <= S_SORT_CMP;
          end
        end
        S_SORT_CMP: begin
          if (e_ab != null && e_cd != null && e_ac != null) begin
            sort_cmp_result_out <= e_ab.sortCmp_sv(e_cd);
            void'(e_ac.sortCmp_sv(e_cd));
          end
          edge_op_state <= S_DELETE_EDGE;
        end
        S_DELETE_EDGE: begin
          if (delete_edge_cmd) begin
            if (e_ab != null) begin my_graph.remove_edge(e_ab); e_ab.unlinkDelete_sv(); e_ab = null; end
            if (e_bc != null) begin my_graph.remove_edge(e_bc); e_bc.unlinkDelete_sv(); e_bc = null; end
          end
          edge_op_state <= S_DONE;
        end
        S_DONE: begin
        end
      endcase
      current_edge_count_out <= my_graph.get_edge_count();
    end
  end
endmodule
module GraphUtilityOps (
  input logic clk,
  input logic rst_n,
  input int   operation_code,
  output int  graph_state_value_out
);
  Graph_SV my_graph;
  GraphVertex_SV initial_vtx_a, initial_vtx_b, initial_vtx_c;
  GraphEdge_SV initial_edge_ab, initial_edge_bc;
  bit graph_initialized;
  localparam OP_CLEAR_ALL            = 1;
  localparam OP_USER_CLEAR_VERTICES  = 2;
  localparam OP_USER_CLEAR_EDGES     = 3;
  localparam OP_CLEAR_COLORS         = 4;
  localparam OP_DUMP                 = 5;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      my_graph = null;
      initial_vtx_a = null; initial_vtx_b = null; initial_vtx_c = null;
      initial_edge_ab = null; initial_edge_bc = null;
      graph_initialized <= 0;
      graph_state_value_out <= 0;
    end else begin
      if (!graph_initialized) begin
        my_graph = new();
        initial_vtx_a = new("UtilVA", 1, 10);
        initial_vtx_b = new("UtilVB", 2, 20);
        initial_vtx_c = new("UtilVC", 0, 30);
        my_graph.add_vertex(initial_vtx_a);
        my_graph.add_vertex(initial_vtx_b);
        my_graph.add_vertex(initial_vtx_c);
        initial_edge_ab = new(initial_vtx_a, initial_vtx_b, 5, 1'b1);
        initial_edge_bc = new(initial_vtx_b, initial_vtx_c, 0, 1'b0);
        my_graph.add_edge(initial_edge_ab);
        my_graph.add_edge(initial_edge_bc);
        initial_vtx_a.set_user_int(99);
        initial_edge_ab.set_user_int(101);
        graph_initialized <= 1;
      end
      case (operation_code)
        OP_CLEAR_ALL: begin
          if (my_graph != null) my_graph.clear_sv();
          graph_state_value_out <= 1;
          graph_initialized <= 0;
        end
        OP_USER_CLEAR_VERTICES: begin
          if (my_graph != null) my_graph.userClearVertices_sv();
          graph_state_value_out <= 2;
        end
        OP_USER_CLEAR_EDGES: begin
          if (my_graph != null) my_graph.userClearEdges_sv();
          graph_state_value_out <= 3;
        end
        OP_CLEAR_COLORS: begin
          if (my_graph != null) my_graph.clearColors_sv();
          graph_state_value_out <= 4;
        end
        OP_DUMP: begin
            if (my_graph != null) begin
                my_graph.dump_graph_sv("Module_Utility_Ops_Dump", 1'b1);
                my_graph.dump_graph_sv("Module_Utility_Ops_Dump_NoColorSub", 1'b0);
            end
            graph_state_value_out <= 5;
        end
        default: begin
          graph_state_value_out <= 0;
        end
      endcase
    end
  end
endmodule
module AdvancedGraphOps (
  input logic clk,
  input logic rst_n,
  input logic trigger_reroute,
  input logic check_connection,
  input logic trigger_error_fatal_cmd,
  input logic trigger_error_nonfatal_cmd,
  input logic trigger_loops_report_cmd,
  output bit   connection_found_out,
  output int   error_status_out
);
  Graph_SV my_graph;
  GraphVertex_SV v_src, v_mid, v_sink, v_isolated;
  GraphEdge_SV e_s_m, e_m_t, e_s_t;
  int op_state;
  bit graph_initialized_adv;
  localparam S_IDLE = 0;
  localparam S_INIT = 1;
  localparam S_REROUTE = 2;
  localparam S_CHECK_CONN = 3;
  localparam S_TRIGGER_ERROR = 4;
  localparam S_REPORT_LOOPS = 5;
  localparam S_DONE = 6;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      my_graph = null;
      op_state <= S_IDLE;
      connection_found_out <= 0;
      error_status_out <= 0;
      v_src = null; v_mid = null; v_sink = null; v_isolated = null;
      e_s_m = null; e_m_t = null; e_s_t = null;
      graph_initialized_adv <= 0;
    end else begin
      if (!graph_initialized_adv) begin
        my_graph = new();
        v_src = new("Source", 1, 1); my_graph.add_vertex(v_src);
        v_mid = new("Middle", 2, 2); my_graph.add_vertex(v_mid);
        v_sink = new("Sink", 3, 3); my_graph.add_vertex(v_sink);
        v_isolated = new("Isolated", 0, 0); my_graph.add_vertex(v_isolated);
        e_s_m = new(v_src, v_mid, 10, 1'b1); my_graph.add_edge(e_s_m);
        e_m_t = new(v_mid, v_sink, 20, 1'b1); my_graph.add_edge(e_m_t);
        e_s_t = new(v_src, v_sink, 5, 1'b0);  my_graph.add_edge(e_s_t);
        graph_initialized_adv <= 1;
        op_state <= S_REROUTE;
      end
      case (op_state)
        S_IDLE: begin
          op_state <= S_REROUTE;
        end
        S_INIT: begin
          op_state <= S_REROUTE;
        end
        S_REROUTE: begin
          if (trigger_reroute && v_mid != null) begin
            v_mid.rerouteEdges_sv(my_graph);
          end
          op_state <= S_CHECK_CONN;
        end
        S_CHECK_CONN: begin
          if (check_connection && v_src != null && v_sink != null) begin
            GraphEdge_SV found_edge = v_src.findConnectingEdgep_sv(v_sink);
            connection_found_out <= (found_edge != null);
            void'(v_src.findConnectingEdgep_sv(v_isolated));
          end
          op_state <= S_TRIGGER_ERROR;
        end
        S_TRIGGER_ERROR: begin
          if (trigger_error_fatal_cmd && v_isolated != null) begin
            v_isolated.trigger_v3error_sv("Simulated fatal error for isolated vertex", 1'b1);
            error_status_out <= 1;
          end else if (trigger_error_nonfatal_cmd && v_isolated != null) begin
            v_isolated.trigger_v3error_sv("Simulated non-fatal error for isolated vertex", 1'b0);
            error_status_out <= 2;
          end else begin
            error_status_out <= 0;
          end
          op_state <= S_REPORT_LOOPS;
        end
        S_REPORT_LOOPS: begin
          if (trigger_loops_report_cmd && v_src != null) begin
            void'(my_graph.reportLoops_sv(v_src));
          end
          op_state <= S_DONE;
        end
        S_DONE: begin
        end
      endcase
    end
  end
endmodule
