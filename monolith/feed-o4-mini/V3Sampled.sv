package ast_pkg;
typedef struct {string name; int depth;} AstScope_t;
typedef struct {AstScope_t scope; string expr;} AstSampled_t;
typedef struct {string varname; bit readOnly;} AstVarRef_t;
typedef struct {string name; AstScope_t scope; bit user1Set;} AstVarScope_t;
class SampledVisitor;
  protected AstScope_t m_scope;
  protected bit m_inSampled;
  function new(); m_inSampled = 0; endfunction
  function AstVarScope_t createSampledVar(AstVarScope_t vscp);
    AstVarScope_t newvscp;
    newvscp.name = {"__Vsampled_", vscp.scope.name, "__", vscp.name};
    newvscp.scope = m_scope;
    newvscp.user1Set = 1;
    return newvscp;
  endfunction
  function void visitScope(AstScope_t scope_in);
    AstScope_t old_scope = m_scope;
    m_scope = scope_in;
    m_scope = old_scope;
  endfunction
  function AstSampled_t visitSampled(AstSampled_t node);
    bit old_in;
    AstSampled_t result;
    old_in = m_inSampled;
    m_inSampled = 1;
    result = node;
    m_inSampled = old_in;
    return result;
  endfunction
  function AstVarRef_t visitVarRef(AstVarRef_t node, AstVarScope_t vscp);
    AstVarRef_t out;
    bit condition;
    condition = m_inSampled && !vscp.user1Set;
    out = node;
    if (condition) begin
      AstVarScope_t lastscp = createSampledVar(vscp);
      out.varname = lastscp.name;
    end
    return out;
  endfunction
  function void sampledAll();
    visitScope('{name:"top", depth:0});
  endfunction
endclass
endpackage
module m_create_sampled_var(input logic clk, input logic rst_n, output logic [31:0] new_name_hash);
  import ast_pkg::*;
  SampledVisitor sv;
  AstVarScope_t vscp, nvscp;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) new_name_hash <= 0;
    else begin
      sv = new();
      vscp.name = "varA";
      vscp.scope.name = "scopeA";
      vscp.scope.depth = 1;
      vscp.user1Set = 0;
      nvscp = sv.createSampledVar(vscp);
      new_name_hash <= nvscp.name.len() * 31 + nvscp.scope.depth;
    end
  end
endmodule
module m_visit_scope(input logic [31:0] in_depth, output logic [31:0] out_depth);
  import ast_pkg::*;
  SampledVisitor sv;
  AstScope_t sc_in;
  always_comb begin
    sv = new();
    sc_in.name = "myscope";
    sc_in.depth = in_depth;
    sv.visitScope(sc_in);
    out_depth = sc_in.depth + 1;
  end
endmodule
module m_visit_sampled(input logic [7:0] expr_in, output logic [15:0] expr_out);
  import ast_pkg::*;
  SampledVisitor sv;
  AstSampled_t node_in, node_out;
  bit [31:0] len;
  always_comb begin
    sv = new();
    node_in.scope.name = "";
    node_in.scope.depth = 0;
    node_in.expr = {"E", expr_in};
    len = node_in.expr.len();
    node_out = sv.visitSampled(node_in);
    expr_out = expr_in + len;
  end
endmodule
module m_visit_var_ref(input logic in_flag, input logic [15:0] varid, output logic [15:0] out_varid);
  import ast_pkg::*;
  SampledVisitor sv;
  AstVarRef_t node, newnode;
  AstVarScope_t vsco;
  always_comb begin
    sv = new();
    vsco.name = "vref";
    vsco.scope.name = "scopeV";
    vsco.scope.depth = 2;
    vsco.user1Set = 0;
    node.varname = "vref";
    node.readOnly = 1;
    if (in_flag) begin
      newnode = sv.visitVarRef(node, vsco);
      out_varid = newnode.varname.len() + vsco.scope.depth;
    end else begin
      out_varid = varid;
    end
  end
endmodule
module m_sampled_all(input logic en, output logic done);
  import ast_pkg::*;
  SampledVisitor sv;
  always_comb begin
    sv = new();
    if (en) begin
      sv.sampledAll();
      done = 1;
    end else done = 0;
  end
endmodule
