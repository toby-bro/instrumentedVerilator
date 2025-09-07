module debug_domain (
    input  logic deleteDomain,
    input  logic hasCombo,
    input  logic isMulti,
    output logic [7:0] code
);
    always_comb begin
        if (deleteDomain)
            code = 8'h44;
        else if (hasCombo)
            code = 8'h43;
        else if (isMulti)
            code = 8'h4D;
        else
            code = 8'h4E;
    end
endmodule
module combine_domains (
    input  logic ap_eq_bp,
    input  logic ap_delete,
    input  logic bp_delete,
    input  logic ap_backp,
    input  logic bp_backp,
    output logic senTreep_clone,
    output logic add_senses_clone,
    output logic unlink_and_delete
);
    always_comb begin
        senTreep_clone      = 0;
        add_senses_clone    = 0;
        unlink_and_delete   = 0;
        if (ap_eq_bp) begin
        end else if (ap_delete) begin
        end else begin
            assert (!bp_delete);
            if (ap_backp)
                senTreep_clone = 1;
            if (bp_backp)
                add_senses_clone = 1;
            else
                unlink_and_delete = 1;
        end
    end
endmodule
module simplify_domain (
    input  logic senTree_backp,
    output logic constified,
    output logic multi_flag,
    output logic get_tree_clone,
    output logic delete_orig
);
    always_comb begin
        constified      = 0;
        multi_flag      = 0;
        get_tree_clone  = 0;
        delete_orig     = 0;
        if (!senTree_backp) begin
            constified     = 1;
            multi_flag     = 1;
            get_tree_clone = 1;
            delete_orig    = 1;
        end
    end
endmodule
module process_domains_sample #(
    parameter int MAX_V = 8,
    parameter int MAX_E = 4
) (
    input  logic domain_set_in    [MAX_V],
    input  logic weight           [MAX_V][MAX_E],
    input  logic domain_matters   [MAX_V],
    input  logic is_logic         [MAX_V],
    input  logic var_vertex       [MAX_V],
    input  logic delete_domain    [MAX_V],
    output logic domain_set_out   [MAX_V],
    output logic to_delete        [MAX_V]
);
    logic domain     [MAX_V];
    logic new_domain;
    int i, j;
    always_comb begin
        for (i = 0; i < MAX_V; i++) begin
            new_domain         = 0;
            domain[i]          = domain_set_in[i];
            if (domain_set_in[i])
                new_domain = domain_set_in[i];
            else if (is_logic[i])
                new_domain = 1;
            for (j = 0; j < MAX_E; j++) begin
                if (weight[i][j] && domain_matters[j]) begin
                    if (domain[j] == delete_domain[j]) begin
                    end else if (!new_domain) begin
                        new_domain = domain[j];
                    end else begin
                        new_domain = new_domain ^ domain[j];
                    end
                end
            end
            if (!new_domain) begin
                to_delete[i]         = 1;
                domain_set_out[i]    = delete_domain[i];
            end else begin
                domain_set_out[i]    = new_domain;
                to_delete[i]         = 0;
            end
        end
    end
endmodule
module process_edge_report #(
    parameter int MAX_V = 8
) (
    input  logic var_vertex       [MAX_V],
    input  logic is_pre           [MAX_V],
    input  logic is_post          [MAX_V],
    input  logic is_pord          [MAX_V],
    input  logic [1:0] domain_type[MAX_V],
    output int   report_count
);
    string report[$];
    int i;
    always_comb begin
        report = {};
        for (i = 0; i < MAX_V; i++) begin
            if (var_vertex[i]) begin
                string name = $sformatf("vtx%0d", i);
                if (is_pre[i])
                    name = {name, " {PRE}"};
                else if (is_post[i])
                    name = {name, " {POST}"};
                else if (is_pord[i])
                    name = {name, " {PORD}"};
                string line;
                if (domain_type[i] == 2'b00)
                    line = {name, ": DELETED"};
                else
                    line = name;
                report.push_back(line);
            end
        end
        report_count = report.size();
    end
endmodule
module apply_invoker (
    input  logic enable,
    output logic done
);
    always_comb begin
        if (enable)
            done = 1;
        else
            done = 0;
    end
endmodule
