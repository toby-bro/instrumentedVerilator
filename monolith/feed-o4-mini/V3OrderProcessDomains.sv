module debug_domain_mod (
    input  logic [63:0] domainp,
    input  logic        m_deleteDomain_flag,
    input  logic        hasCombo,
    input  logic        isMulti,
    output logic [1:0]  flag
);
   always_comb begin
      if (domainp == 64'h1 && m_deleteDomain_flag) begin
         flag = 2'b01;
      end else if (hasCombo) begin
         flag = 2'b10;
      end else if (isMulti) begin
         flag = 2'b11;
      end else begin
         flag = 2'b00;
      end
   end
endmodule
module combine_domains_mod (
    input  logic        ap_backp,
    input  logic        bp_backp,
    output logic        senTreep_backp
);
   class AstSenTree;
      bit backp;
      function new(bit b); backp = b; endfunction
      function AstSenTree cloneTree(bit omit_back);
         AstSenTree c = new(backp);
         return c;
      endfunction
      function void addSensesp(AstSenTree sen); endfunction
      function AstSenTree unlinkFrBackWithNext();
         return this;
      endfunction
      function void deleteTree(); endfunction
   endclass
   always_comb begin
      AstSenTree ap;
      AstSenTree bp;
      AstSenTree senTreep;
      ap = new(ap_backp);
      bp = new(bp_backp);
      if (ap.backp) begin
         senTreep = ap.cloneTree(0);
      end else begin
         senTreep = ap;
      end
      if (bp.backp) begin
         senTreep.addSensesp(bp.cloneTree(1));
      end else begin
         senTreep.addSensesp(bp.unlinkFrBackWithNext());
         bp.deleteTree();
      end
      senTreep_backp = senTreep.backp;
   end
endmodule
module simplify_domain_mod (
    input  logic        senTreep_backp_in,
    output logic        resultp_backp_out
);
   class AstSenTree;
      bit backp;
      function new(bit b); backp = b; endfunction
      function void multi(bit m); endfunction
      function AstSenTree cloneTree();
         return new(backp);
      endfunction
      function void deleteTree(); endfunction
   endclass
   class V3Const;
      static function void constifyExpensiveEdit(ref AstSenTree s); endfunction
   endclass
   class SenTreeFinder;
      function new(); endfunction
      function AstSenTree getSenTree(AstSenTree tr);
         return tr.cloneTree();
      endfunction
   endclass
   always_comb begin
      AstSenTree senTreep;
      SenTreeFinder finder;
      AstSenTree resultp;
      senTreep = new(senTreep_backp_in);
      if (senTreep.backp) begin
         resultp_backp_out = senTreep.backp;
      end else begin
         V3Const::constifyExpensiveEdit(senTreep);
         senTreep.multi(1);
         finder = new();
         resultp = finder.getSenTree(senTreep);
         senTreep.deleteTree();
         resultp_backp_out = resultp.backp;
      end
   end
endmodule
module process_domains_mod #(
    parameter int N = 8
) (
    input  logic              clk,
    input  logic              rst_n,
    input  logic [N-1:0]      vertex_valid,
    input  logic [N-1:0]      domain_assigned,
    output logic [N-1:0]      domainp_deleted
);
   typedef struct { bit domainMatters; bit deleted; } OrderEitherVertex;
   OrderEitherVertex vertices [N];
   always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n) begin
         int i;
         for (i = 0; i < N; i++) begin
            vertices[i].domainMatters <= 1;
            vertices[i].deleted      <= 0;
            domainp_deleted[i]       <= 0;
         end
      end else begin
         int idx;
         for (idx = 0; idx < N; idx++) begin
            bit domp;
            logic [$clog2(N)-1:0] inEdges[$];
            int j;
            domp = 0;
            if (idx > 0) inEdges.push_back(idx-1);
            for (j = 0; j < inEdges.size(); j++) begin
               bit from_domain;
               from_domain = domain_assigned[inEdges[j]];
               if (from_domain && !vertices[inEdges[j]].domainMatters) continue;
               if (!domp) domp = from_domain;
               else domp = domp & from_domain;
            end
            if (!vertex_valid[idx]) begin
               domainp_deleted[idx] <= 0;
            end else if (domain_assigned[idx]) begin
               domainp_deleted[idx] <= 0;
            end else if (!domp) begin
               vertices[idx].deleted <= 1;
               domainp_deleted[idx]  <= 1;
            end else begin
               domainp_deleted[idx]  <= 0;
            end
         end
      end
   end
endmodule
module process_edge_report_mod #(
    parameter int MAXV = 16
) (
    input  logic [MAXV-1:0] varValid,
    input  logic [MAXV-1:0] deletedFlags,
    output logic [31:0]     report_count
);
   typedef struct {
      logic [31:0] ptr;
      string       name;
      bit          isPre;
      bit          isPost;
   } VarVertex;
   VarVertex varList [MAXV];
   string reportQueue [$];
   always_comb begin
      int i;
      int a;
      int b;
      string entry;
      string nm;
      string tmp;
      reportQueue.delete();
      for (i = 0; i < MAXV; i++) begin
         if (!varValid[i]) continue;
         nm = varList[i].name;
         if (varList[i].isPre) nm = {nm, "_PRE"};
         else if (varList[i].isPost) nm = {nm, "_POST"};
         entry = $sformatf("%0h %s", varList[i].ptr, nm);
         if (deletedFlags[i]) entry = {entry, " DELETED"};
         reportQueue.push_back(entry);
      end
      for (a = 0; a < reportQueue.size(); a++) begin
         for (b = a+1; b < reportQueue.size(); b++) begin
            if (reportQueue[a] > reportQueue[b]) begin
               tmp = reportQueue[a];
               reportQueue[a] = reportQueue[b];
               reportQueue[b] = tmp;
            end
         end
      end
      report_count = reportQueue.size();
   end
endmodule
module apply_mod (
    input  logic kick,
    input  logic valid,
    output logic done
);
   function void applyFunc(input bit k, input bit v, output bit d);
      d = k & v;
   endfunction
   always_comb begin
      applyFunc(kick, valid, done);
   end
endmodule
