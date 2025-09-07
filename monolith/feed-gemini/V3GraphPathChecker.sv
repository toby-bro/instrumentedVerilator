typedef enum {
    FORWARD_WAY = 0,
    REVERSE_WAY = 1,
    NUM_WAYS_E = 2
} GraphWay_e;
function automatic GraphWay_e invert_way(GraphWay_e way);
    if (way == FORWARD_WAY) return REVERSE_WAY;
    return FORWARD_WAY;
endfunction
typedef class V3GraphVertex;
typedef class V3GraphEdge;
typedef V3GraphEdge V3GraphEdge_h;
typedef V3GraphEdge_h V3GraphEdge_h_queue[$];
class GraphPCNode;
    logic [31:0] m_cp [NUM_WAYS_E];
    longint unsigned m_seenAtGeneration;
    function new();
        foreach (m_cp[i]) m_cp[i] = 0;
        m_seenAtGeneration = 0;
    endfunction
endclass
class V3GraphEdge;
    V3GraphVertex from_v;
    V3GraphVertex to_v;
    bit enabled_edge;
    function new(V3GraphVertex from_v_in, V3GraphVertex to_v_in, bit enabled = 1'b1);
        this.from_v = from_v_in;
        this.to_v = to_v_in;
        this.enabled_edge = enabled;
    endfunction
    function automatic V3GraphVertex fromp(); return from_v; endfunction
    function automatic V3GraphVertex top(); return to_v; endfunction
    function automatic V3GraphVertex furtherp(GraphWay_e way);
        if (way == FORWARD_WAY) return to_v;
        else return from_v;
    endfunction
endclass
class V3GraphVertex;
    string name;
    GraphPCNode user_data;
    V3GraphEdge_h_queue out_edges;
    V3GraphEdge_h_queue in_edges;
    function new(string name_in = "");
        this.name = name_in;
        user_data = new();
    endfunction
    function automatic V3GraphEdge_h_queue get_edges(GraphWay_e way);
        if (way == FORWARD_WAY) return out_edges;
        else return in_edges;
    endfunction
    function automatic void add_out_edge(V3GraphEdge_h edge_handle);
        out_edges.push_back(edge_handle);
    endfunction
    function automatic void add_in_edge(V3GraphEdge_h edge_handle);
        in_edges.push_back(edge_handle);
    endfunction
endclass
class V3Graph;
    V3GraphVertex vertices[$];
    function new();
    endfunction
    function automatic void add_vertex(V3GraphVertex v);
        vertices.push_back(v);
    endfunction
    function automatic int num_vertices();
        return vertices.size();
    endfunction
endclass
virtual class IEdgeFunction;
    pure virtual function bit check_edge(V3GraphEdge_h edge_handle);
endclass
class GlobalEdgeFunc extends IEdgeFunction;
    virtual function bit check_edge(V3GraphEdge_h edge_handle);
        return edge_handle.enabled_edge;
    endfunction
endclass
class GraphPathChecker;
    V3Graph m_graphp;
    IEdgeFunction m_edgeFuncp;
    longint unsigned m_generation;
    function new(V3Graph graphp_in, IEdgeFunction edgeFuncp_in);
        this.m_graphp = graphp_in;
        this.m_edgeFuncp = edgeFuncp_in;
        this.m_generation = 0;
        void'(initHalfCriticalPaths(FORWARD_WAY, 1'b0));
        void'(initHalfCriticalPaths(REVERSE_WAY, 1'b0));
    endfunction
    function void delete_nodes();
        foreach (m_graphp.vertices[i]) begin
            m_graphp.vertices[i].user_data = null;
        end
        m_graphp.vertices.delete();
    endfunction
    function automatic bit initHalfCriticalPaths(GraphWay_e N_Way, bit checkOnly);
        GraphWay_e way = N_Way;
        GraphWay_e rev = invert_way(way);
        logic [31:0] critPathCost;
        V3GraphVertex vertexp;
        V3GraphEdge_h_queue edges_to_process;
        V3GraphEdge_h edge_h;
        V3GraphVertex wrelativep;
        GraphPCNode wrelUserp;
        GraphPCNode ourUserp;
        int j;
        foreach (m_graphp.vertices[i]) begin
            vertexp = m_graphp.vertices[i];
            critPathCost = 0;
            edges_to_process = vertexp.get_edges(rev);
            foreach (edges_to_process[j]) begin
                edge_h = edges_to_process[j];
                if (!m_edgeFuncp.check_edge(edge_h)) continue;
                wrelativep = edge_h.furtherp(rev);
                wrelUserp = wrelativep.user_data;
                critPathCost = (critPathCost > wrelUserp.m_cp[way] + 1) ? critPathCost : (wrelUserp.m_cp[way] + 1);
            end
            ourUserp = vertexp.user_data;
            if (checkOnly) begin
                if (ourUserp.m_cp[way] != critPathCost) begin
                    return 1'b1;
                end
            end else begin
                ourUserp.m_cp[way] = critPathCost;
            end
        end
        return 1'b0;
    endfunction
    function automatic bit pathExistsInternal(V3GraphVertex ap, V3GraphVertex bp, output int unsigned costp);
        GraphPCNode auserp;
        GraphPCNode buserp;
        bit foundPath;
        V3GraphEdge_h edge_h;
        int unsigned childCost;
        int i;
        auserp = ap.user_data;
        buserp = bp.user_data;
        foundPath = 0;
        costp = 0;
        if (auserp.m_seenAtGeneration == m_generation) begin
            costp = 0;
            return 0;
        end
        auserp.m_seenAtGeneration = m_generation;
        costp = 1;
        if (ap == bp) return 1;
        if (auserp.m_cp[REVERSE_WAY] < buserp.m_cp[REVERSE_WAY] + 1) return 0;
        if (buserp.m_cp[FORWARD_WAY] < auserp.m_cp[FORWARD_WAY] + 1) return 0;
        foreach (ap.out_edges[i]) begin
            edge_h = ap.out_edges[i];
            if (!m_edgeFuncp.check_edge(edge_h)) continue;
            if (pathExistsInternal(edge_h.to_v, bp, childCost)) foundPath = 1;
            costp = costp + childCost;
        end
        return foundPath;
    endfunction
    function automatic bit pathExistsFrom(V3GraphVertex fromp, V3GraphVertex top);
        int unsigned cost;
        incGeneration();
        return pathExistsInternal(fromp, top, cost);
    endfunction
    function automatic bit isTransitiveEdge(V3GraphEdge_h edgep);
        V3GraphVertex fromp;
        V3GraphVertex top;
        V3GraphEdge_h fromOut_h;
        int unsigned cost;
        int i;
        fromp = edgep.from_v;
        top = edgep.to_v;
        incGeneration();
        foreach (fromp.out_edges[i]) begin
            fromOut_h = fromp.out_edges[i];
            if (fromOut_h == edgep) continue;
            if (pathExistsInternal(fromOut_h.to_v, top, cost)) return 1;
        end
        return 0;
    endfunction
    function void incGeneration();
        m_generation++;
    endfunction
endclass
module CriticalPathInitializerModule (
    input logic enable_check_only,
    output logic [31:0] final_cp_A_fwd,
    output logic [31:0] final_cp_B_rev,
    output logic init_success
);
  always_comb begin : main_block
    V3Graph my_graph;
    V3GraphVertex vA, vB, vC;
    V3GraphEdge_h eAB, eBC;
    GraphPathChecker path_checker;
    IEdgeFunction edge_func_inst;
    bit temp_validation_result;
    vA = new("A");
    vB = new("B");
    vC = new("C");
    eAB = new(vA, vB);
    eBC = new(vB, vC);
    vA.add_out_edge(eAB);
    vB.add_out_edge(eBC);
    vB.add_in_edge(eAB);
    vC.add_in_edge(eBC);
    my_graph = new();
    my_graph.add_vertex(vA);
    my_graph.add_vertex(vB);
    my_graph.add_vertex(vC);
    GlobalEdgeFunc concrete_edge_func_h = new GlobalEdgeFunc();
    edge_func_inst = concrete_edge_func_h;
    path_checker = new(my_graph, edge_func_inst);
    void'(path_checker.initHalfCriticalPaths(REVERSE_WAY, enable_check_only));
    temp_validation_result = path_checker.initHalfCriticalPaths(FORWARD_WAY, enable_check_only);
    final_cp_A_fwd = vA.user_data.m_cp[FORWARD_WAY];
    final_cp_B_rev = vB.user_data.m_cp[REVERSE_WAY];
    init_success = (final_cp_A_fwd == 0 && final_cp_B_rev == 1 && !temp_validation_result);
    path_checker.delete_nodes();
  end
endmodule
module PathExistenceCheckerModule (
    input logic enable_cycle,
    input logic disable_edge_BC,
    output logic path_A_to_C_exists,
    output logic path_A_to_A_exists,
    output int unsigned path_A_to_C_cost_out
);
  always_comb begin : main_block
    V3Graph my_graph;
    V3GraphVertex vA, vB, vC, vD;
    V3GraphEdge_h eAB, eBC, eBD, eDA;
    GraphPathChecker path_checker;
    IEdgeFunction edge_func_inst;
    path_A_to_C_exists = 0;
    path_A_to_A_exists = 0;
    path_A_to_C_cost_out = 0;
    vA = new("A");
    vB = new("B");
    vC = new("C");
    vD = new("D");
    eAB = new(vA, vB);
    eBC = new(vB, vC, !disable_edge_BC);
    eBD = new(vB, vD);
    eDA = new(vD, vA);
    vA.add_out_edge(eAB);
    vB.add_out_edge(eBC);
    vB.add_out_edge(eBD);
    vB.add_in_edge(eAB);
    vC.add_in_edge(eBC);
    vD.add_in_edge(eBD);
    if (enable_cycle) begin
      vD.add_out_edge(eDA);
      vA.add_in_edge(eDA);
    end
    my_graph = new();
    my_graph.add_vertex(vA);
    my_graph.add_vertex(vB);
    my_graph.add_vertex(vC);
    my_graph.add_vertex(vD);
    GlobalEdgeFunc concrete_edge_func_h = new GlobalEdgeFunc();
    edge_func_inst = concrete_edge_func_h;
    path_checker = new(my_graph, edge_func_inst);
    path_A_to_C_exists = path_checker.pathExistsFrom(vA, vC);
    path_checker.incGeneration(); 
    void'(path_checker.pathExistsInternal(vA, vC, path_A_to_C_cost_out));
    path_checker.incGeneration(); 
    path_A_to_A_exists = path_checker.pathExistsFrom(vA, vA);
    path_checker.delete_nodes();
  end
endmodule
module TransitiveEdgeCheckerModule (
    input logic disable_direct_edge_for_transitive,
    output logic is_eAC_transitive_out,
    output logic is_eAB_not_transitive_out
);
  always_comb begin : main_block
    V3Graph my_graph;
    V3GraphVertex vA, vB, vC, vD;
    V3GraphEdge_h eAB, eBC, eAC_direct, eAD, eDC;
    GraphPathChecker path_checker;
    IEdgeFunction edge_func_inst;
    is_eAC_transitive_out = 0;
    is_eAB_not_transitive_out = 0;
    vA = new("A");
    vB = new("B");
    vC = new("C");
    vD = new("D");
    eAB = new(vA, vB);
    eBC = new(vB, vC);
    eAC_direct = new(vA, vC, !disable_direct_edge_for_transitive);
    eAD = new(vA, vD);
    eDC = new(vD, vC);
    vA.add_out_edge(eAB);
    vA.add_out_edge(eAC_direct);
    vA.add_out_edge(eAD);
    vB.add_out_edge(eBC);
    vD.add_out_edge(eDC);
    vB.add_in_edge(eAB);
    vC.add_in_edge(eBC);
    vC.add_in_edge(eAC_direct);
    vC.add_in_edge(eDC);
    vD.add_in_edge(eAD);
    my_graph = new();
    my_graph.add_vertex(vA);
    my_graph.add_vertex(vB);
    my_graph.add_vertex(vC);
    my_graph.add_vertex(vD);
    GlobalEdgeFunc concrete_edge_func_h = new GlobalEdgeFunc();
    edge_func_inst = concrete_edge_func_h;
    path_checker = new(my_graph, edge_func_inst);
    is_eAC_transitive_out = path_checker.isTransitiveEdge(eAC_direct);
    is_eAB_not_transitive_out = !path_checker.isTransitiveEdge(eAB);
    path_checker.delete_nodes();
  end
endmodule
module CriticalPathValidationFailureModule (
    input logic trigger_validation,
    output logic validation_failure_flag
);
  always_comb begin : main_block
    V3Graph my_graph;
    V3GraphVertex vA, vB;
    V3GraphEdge_h eAB;
    GraphPathChecker path_checker;
    IEdgeFunction edge_func_inst;
    bit check_result;
    validation_failure_flag = 0;
    vA = new("A");
    vB = new("B");
    eAB = new(vA, vB);
    vA.add_out_edge(eAB);
    vB.add_in_edge(eAB);
    my_graph = new();
    my_graph.add_vertex(vA);
    my_graph.add_vertex(vB);
    GlobalEdgeFunc concrete_edge_func_h = new GlobalEdgeFunc();
    edge_func_inst = concrete_edge_func_h;
    path_checker = new(my_graph, edge_func_inst);
    if (trigger_validation) begin
      vB.user_data.m_cp[FORWARD_WAY] = 10;
    end
    check_result = path_checker.initHalfCriticalPaths(FORWARD_WAY, 1'b1);
    validation_failure_flag = check_result;
    path_checker.delete_nodes();
  end
endmodule
