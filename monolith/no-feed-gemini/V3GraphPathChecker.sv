module PathExistenceChecker #(
    parameter NUM_VERTICES = 5,
    parameter MAX_OUT_EDGES = 3 
) (
    input logic clk, 
    input logic rst_n, 
    input logic [NUM_VERTICES-1:0] i_from_node, 
    input logic [NUM_VERTICES-1:0] i_to_node,   
    input logic i_check_path,                   
    input logic i_enable_all_edges,             
    output logic o_path_exists,                 
    output logic [31:0] o_total_cost            
);
    logic [NUM_VERTICES-1:0][MAX_OUT_EDGES-1:0] graph_edges;
    logic [31:0] critical_path_forward [NUM_VERTICES]; 
    logic [31:0] critical_path_reverse [NUM_VERTICES]; 
    logic [63:0] seen_at_generation [NUM_VERTICES]; 
    logic [63:0] current_generation_val; 
    function automatic logic edge_func(logic [NUM_VERTICES-1:0] edge_from, logic [NUM_VERTICES-1:0] edge_to);
        if (!i_enable_all_edges && edge_from == 0 && edge_to == 1) begin
            return 1'b0; 
        end
        return 1'b1; 
    endfunction
    always_comb begin
        graph_edges[0] = {2, 1, NUM_VERTICES}; 
        graph_edges[1] = {3, NUM_VERTICES, NUM_VERTICES}; 
        graph_edges[2] = {3, NUM_VERTICES, NUM_VERTICES}; 
        graph_edges[3] = {4, NUM_VERTICES, NUM_VERTICES}; 
        graph_edges[4] = {NUM_VERTICES, NUM_VERTICES, NUM_VERTICES}; 
        critical_path_forward[4] = 0; 
        critical_path_forward[3] = 1; 
        critical_path_forward[1] = 2; 
        critical_path_forward[2] = 2; 
        critical_path_forward[0] = 3; 
        critical_path_reverse[0] = 0; 
        critical_path_reverse[1] = 1; 
        critical_path_reverse[2] = 1; 
        critical_path_reverse[3] = 2; 
        critical_path_reverse[4] = 3; 
    end
    function automatic logic path_exists_internal(
        input logic [NUM_VERTICES-1:0] ap,
        input logic [NUM_VERTICES-1:0] bp,
        output logic [31:0] costp
    );
        logic found_path_local;
        logic [31:0] child_cost;
        if (ap >= NUM_VERTICES || bp >= NUM_VERTICES) begin
             costp = 0; return 1'b0; 
        end
        if (seen_at_generation[ap] == current_generation_val) begin
            costp = 0;
            return 1'b0; 
        end
        seen_at_generation[ap] = current_generation_val;
        costp = 1; 
        if (ap == bp) begin 
            return 1'b1;
        end
        if (critical_path_reverse[ap] < (critical_path_reverse[bp] + 1)) begin
            return 1'b0;
        end
        if (critical_path_forward[bp] < (critical_path_forward[ap] + 1)) begin
            return 1'b0;
        end
        found_path_local = 1'b0; 
        for (int i = 0; i < MAX_OUT_EDGES; i++) begin
            logic [NUM_VERTICES-1:0] next_node = graph_edges[ap][i];
            if (next_node == NUM_VERTICES) continue; 
            if (!edge_func(ap, next_node)) begin
                continue; 
            end
            if (path_exists_internal(next_node, bp, child_cost)) begin
                found_path_local = 1'b1;
            end
            costp += child_cost; 
        end
        return found_path_local; 
    endfunction
    function automatic logic path_exists_from(
        input logic [NUM_VERTICES-1:0] fromp,
        input logic [NUM_VERTICES-1:0] top,
        output logic [31:0] cost
    );
        current_generation_val = current_generation_val + 1;
        cost = 0; 
        return path_exists_internal(fromp, top, cost);
    endfunction
    always_comb begin
        o_path_exists = 1'b0;
        o_total_cost = 0;
        if (!rst_n) begin
            current_generation_val = 0;
            for (int i = 0; i < NUM_VERTICES; i++) begin
                seen_at_generation[i] = 0;
            end
        end else begin
            if (i_check_path) begin
                o_path_exists = path_exists_from(i_from_node, i_to_node, o_total_cost);
            end
        end
    end
endmodule
module TransitiveEdgeChecker #(
    parameter NUM_VERTICES = 5,
    parameter MAX_OUT_EDGES = 3
) (
    input logic clk, 
    input logic rst_n, 
    input logic [NUM_VERTICES-1:0] i_edge_from_node,   
    input logic [NUM_VERTICES-1:0] i_edge_to_node,     
    input logic i_check_transitivity,                 
    input logic i_enable_all_edges,                   
    output logic o_is_transitive_edge                  
);
    logic [NUM_VERTICES-1:0][MAX_OUT_EDGES-1:0] graph_edges;
    logic [31:0] critical_path_forward [NUM_VERTICES];
    logic [31:0] critical_path_reverse [NUM_VERTICES];
    logic [63:0] seen_at_generation [NUM_VERTICES];
    logic [63:0] current_generation_val;
    function automatic logic edge_func(logic [NUM_VERTICES-1:0] edge_from, logic [NUM_VERTICES-1:0] edge_to);
        if (!i_enable_all_edges && edge_from == 0 && edge_to == 1) begin
            return 1'b0; 
        end
        return 1'b1; 
    endfunction
    always_comb begin
        graph_edges[0] = {2, 1, NUM_VERTICES};
        graph_edges[1] = {3, NUM_VERTICES, NUM_VERTICES};
        graph_edges[2] = {3, NUM_VERTICES, NUM_VERTICES};
        graph_edges[3] = {4, NUM_VERTICES, NUM_VERTICES};
        graph_edges[4] = {NUM_VERTICES, NUM_VERTICES, NUM_VERTICES};
        critical_path_forward[4] = 0; critical_path_forward[3] = 1; critical_path_forward[1] = 2;
        critical_path_forward[2] = 2; critical_path_forward[0] = 3;
        critical_path_reverse[0] = 0; critical_path_reverse[1] = 1; critical_path_reverse[2] = 1;
        critical_path_reverse[3] = 2; critical_path_reverse[4] = 3;
    end
    function automatic logic path_exists_internal(
        input logic [NUM_VERTICES-1:0] ap,
        input logic [NUM_VERTICES-1:0] bp,
        output logic [31:0] costp
    );
        logic found_path_local;
        logic [31:0] child_cost;
        if (ap >= NUM_VERTICES || bp >= NUM_VERTICES) begin
             costp = 0; return 1'b0;
        end
        if (seen_at_generation[ap] == current_generation_val) begin
            costp = 0;
            return 1'b0;
        end
        seen_at_generation[ap] = current_generation_val;
        costp = 1;
        if (ap == bp) begin
            return 1'b1;
        end
        if (critical_path_reverse[ap] < (critical_path_reverse[bp] + 1)) begin
            return 1'b0;
        end
        if (critical_path_forward[bp] < (critical_path_forward[ap] + 1)) begin
            return 1'b0;
        end
        found_path_local = 1'b0;
        for (int i = 0; i < MAX_OUT_EDGES; i++) begin
            logic [NUM_VERTICES-1:0] next_node = graph_edges[ap][i];
            if (next_node == NUM_VERTICES) continue;
            if (!edge_func(ap, next_node)) begin
                continue; 
            end
            if (path_exists_internal(next_node, bp, child_cost)) begin
                found_path_local = 1'b1;
            end
            costp += child_cost;
        end
        return found_path_local;
    endfunction
    function automatic logic is_transitive_edge_func(
        input logic [NUM_VERTICES-1:0] fromp,
        input logic [NUM_VERTICES-1:0] top
    );
        logic is_transitive;
        logic [31:0] dummy_cost; 
        current_generation_val = current_generation_val + 1;
        is_transitive = 1'b0; 
        for (int i = 0; i < MAX_OUT_EDGES; i++) begin
            logic [NUM_VERTICES-1:0] next_node = graph_edges[fromp][i];
            if (next_node == NUM_VERTICES) continue; 
            if (next_node == top) begin
                continue;
            end
            if (path_exists_internal(next_node, top, dummy_cost)) begin
                is_transitive = 1'b1;
                break; 
            end
        end
        return is_transitive; 
    endfunction
    always_comb begin
        o_is_transitive_edge = 1'b0;
        if (!rst_n) begin
            current_generation_val = 0;
            for (int i = 0; i < NUM_VERTICES; i++) begin
                seen_at_generation[i] = 0;
            end
        end else begin
            if (i_check_transitivity) begin
                o_is_transitive_edge = is_transitive_edge_func(i_edge_from_node, i_edge_to_node);
            end
        end
    end
endmodule
class GraphPCNode_SV;
    rand logic [31:0] m_cp_fw; 
    rand logic [31:0] m_cp_rev; 
    rand logic [63:0] m_seen_gen;
    constraint cp_valid_c {
        m_cp_fw >= 0;
        m_cp_rev >= 0;
    }
    function new();
        m_cp_fw = 0;
        m_cp_rev = 0;
        m_seen_gen = 0;
    endfunction
endclass
module GraphNodeManager #(
    parameter NUM_VERTICES = 5
) (
    input logic clk, 
    input logic rst_n, 
    input logic i_init_nodes, 
    input logic i_free_nodes, 
    input logic [NUM_VERTICES-1:0] i_node_idx, 
    input logic [31:0] i_cp_fw_val, 
    input logic [31:0] i_cp_rev_val, 
    input logic [63:0] i_gen_val, 
    output logic [31:0] o_cp_fw_read, 
    output logic [63:0] o_seen_gen_read, 
    output logic o_node_initialized_status 
);
    GraphPCNode_SV nodes_array [NUM_VERTICES]; 
    logic [NUM_VERTICES-1:0] node_initialized_flags; 
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < NUM_VERTICES; i++) begin
                if (nodes_array[i] != null) begin
                    nodes_array[i] = null; 
                end
                node_initialized_flags[i] = 1'b0;
            end
        end else begin
            if (i_init_nodes) begin
                for (int i = 0; i < NUM_VERTICES; i++) begin
                    if (nodes_array[i] == null) begin 
                        nodes_array[i] = new(); 
                        node_initialized_flags[i] = 1'b1;
                        nodes_array[i].m_cp_fw = i_cp_fw_val + i;
                        nodes_array[i].m_cp_rev = i_cp_rev_val + i;
                        nodes_array[i].m_seen_gen = 0;
                    end
                end
            end else if (i_free_nodes) begin
                for (int i = 0; i < NUM_VERTICES; i++) begin
                    if (nodes_array[i] != null) begin
                        nodes_array[i] = null; 
                    end
                    node_initialized_flags[i] = 1'b0;
                end
            end else if (i_node_idx < NUM_VERTICES && nodes_array[i_node_idx] != null) begin
                nodes_array[i_node_idx].m_cp_fw = i_cp_fw_val;
                nodes_array[i_node_idx].m_cp_rev = i_cp_rev_val;
                nodes_array[i_node_idx].m_seen_gen = i_gen_val;
            end
        end
    end
    assign o_cp_fw_read = (i_node_idx < NUM_VERTICES && nodes_array[i_node_idx] != null) ? nodes_array[i_node_idx].m_cp_fw : 0;
    assign o_seen_gen_read = (i_node_idx < NUM_VERTICES && nodes_array[i_node_idx] != null) ? nodes_array[i_node_idx].m_seen_gen : 0;
    assign o_node_initialized_status = (i_node_idx < NUM_VERTICES) ? node_initialized_flags[i_node_idx] : 1'b0;
endmodule
