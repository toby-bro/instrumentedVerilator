module debug(input logic sig, output logic out);
  assign out = sig;
endmodule
module dumpTreeLevel(input logic [3:0] level, output logic [3:0] out);
  function logic [3:0] f; input logic [3:0] lvl; return lvl; endfunction
  assign out = f(level);
endmodule
module dumpTreeJsonLevel(input logic [4:0] lvl, output logic [4:0] out);
  function automatic logic [4:0] fj; input logic [4:0] l; return {l,1'b0}[4:0]; endfunction
  assign out = fj(lvl);
endmodule
module dumpTreeEitherLevel(input logic en, input logic [2:0] lvl, output logic [2:0] out);
  function logic [2:0] fe(input logic e, input logic [2:0] l); return e ? l : 3'b0; endfunction
  assign out = fe(en,lvl);
endmodule
module cleanupVarRefs(input logic in, output logic out);
  logic tmp;
  always_comb tmp = in;
  assign out = tmp;
endmodule
module visitAstNetlist(input logic clk, input logic rst, output logic done);
  logic [7:0] cnt;
  always_ff @(posedge clk) begin
    if (rst) cnt <= 0;
    else cnt <= cnt + 1;
  end
  assign done = (cnt == 8'hFF);
endmodule
module visitAstNodeModule(input logic en, input logic [3:0] data, output logic [3:0] out);
  generate
    if (en) begin
      assign out = data;
    end else begin
      assign out = 4'b0;
    end
  endgenerate
endmodule
module visitAstClass(input logic a, input logic b, output logic out);
  typedef struct packed { logic x; logic y; } st;
  st s;
  always_comb {s.x,s.y} = {a,b};
  assign out = s.x & s.y;
endmodule
module visitAstCellInline(input logic a, input logic b, output logic out);
  assign out = a | b;
endmodule
module visitAstActive(input logic a, input logic b, output logic out);
  assign out = a & b;
endmodule
module visitAstNodeProcedure(input logic clk, input logic d, output logic q);
  function logic proc(input logic x); return ~x; endfunction
  always_ff @(posedge clk) q <= proc(d);
endmodule
module visitAstAssignAlias(input logic a, output logic b);
  wire alias_a = a;
  assign b = alias_a;
endmodule
module visitAstAssignVarScope(input logic a, output logic [1:0] b);
  logic [1:0] x;
  always_comb x = {2{a}};
  assign b = x;
endmodule
module visitAstAssignW(input logic a, input logic b, output logic out);
  wire w = a & b;
  assign out = w;
endmodule
module visitAstAlwaysPublic(input logic clk, input logic d, output logic q);
  always_ff @(posedge clk) q <= d;
endmodule
module visitAstCoverToggle(input logic clk, input logic e, output logic out);
  cover property @(posedge clk) (e);
  assign out = e;
endmodule
module visitAstCFunc(input logic a, output logic b);
  function logic cfunc(input logic x); return x ^ 1'b1; endfunction
  assign b = cfunc(a);
endmodule
module visitAstNodeFTask(input logic clk, input logic start, output logic gnt);
  task automatic reqtask(input logic s); if (s) gnt <= 1; else gnt <= 0; endtask
  always_ff @(posedge clk) reqtask(start);
endmodule
module visitAstVar(input logic clk, input logic d, output logic q);
  logic varr;
  always_ff @(posedge clk) varr <= d;
  assign q = varr;
endmodule
module visitAstVarRef(input logic [3:0] arr_in, output logic [3:0] arr_out);
  logic [3:0] r;
  always_comb r = arr_in;
  assign arr_out = r;
endmodule
module visitAstScopeName(input logic sel, output logic [7:0] name_code);
  function logic [7:0] getcode(); return sel ? 8'hA5 : 8'h5A; endfunction
  assign name_code = getcode();
endmodule
module visitAstScope(input logic a, input logic b, output logic c);
  always_comb c = a ^ b;
endmodule
module visitAstNode(input logic a, output logic b);
  unique case (a)
    1'b0: b = 0;
    1'b1: b = 1;
  endcase
endmodule
module cleanupVisitor_visitAstScope(input logic a, input logic b, output logic c);
  generate
    if (a & b) assign c = 1;
    else assign c = 0;
  endgenerate
endmodule
module cleanupVisitor_movedDeleteOrIterate(input logic a, input logic b, output logic c);
  logic x,y;
  assign x = a;
  assign y = b;
  assign c = x | y;
endmodule
module cleanupVisitor_visitAstNodeProcedure(input logic clk, input logic d, output logic q);
  always_ff @(posedge clk) q <= d;
endmodule
module cleanupVisitor_visitAstAssignAlias(input logic a, output logic b);
  wire aa = a;
  assign b = aa;
endmodule
module cleanupVisitor_visitAstAssignVarScope(input logic a, output logic b);
  logic tmp;
  always_comb tmp = a;
  assign b = tmp;
endmodule
module cleanupVisitor_visitAstAssignW(input logic a, input logic b, output logic c);
  wire w = a & b;
  assign c = w;
endmodule
module cleanupVisitor_visitAstAlwaysPublic(input logic clk, input logic d, output logic q);
  always_ff @(posedge clk) q <= d;
endmodule
module cleanupVisitor_visitAstCoverToggle(input logic clk, input logic e, output logic out);
  cover property @(posedge clk) (e);
  assign out = e;
endmodule
module cleanupVisitor_visitAstNodeFTask(input logic clk, input logic start, output logic gnt);
  always_ff @(posedge clk) if (start) gnt <= 1; else gnt <= 0;
endmodule
module cleanupVisitor_visitAstCFunc(input logic a, output logic b);
  function logic cf(input logic x); return ~x; endfunction
  assign b = cf(a);
endmodule
module cleanupVisitor_visitAstVarXRef(input logic [3:0] arr, input logic sel, output logic y);
  assign y = arr[sel];
endmodule
module cleanupVisitor_visitAstNodeFTaskRef(input logic clk, input logic call, output logic resp);
  always_ff @(posedge clk) if (call) resp <= 1; else resp <= 0;
endmodule
module cleanupVisitor_visitAstModportFTaskRef(input logic clk, input logic call, output logic done);
  always_ff @(posedge clk) if (call) done <= 1; else done <= 0;
endmodule
module cleanupVisitor_visitAstNodeDefault(input logic a, output logic b);
  assign b = ~a;
endmodule
module v3scope_scopeAll(input logic in, output logic out);
  assign out = in;
endmodule
