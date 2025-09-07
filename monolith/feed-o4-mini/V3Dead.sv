module debug_fn(input logic a, output logic b);
  parameter int ID = 1;
  typedef enum logic [1:0] {D_IDLE, D_RUN} state_t;
  localparam state_t init = D_IDLE;
  assign b = a ? init : D_RUN;
endmodule
module dumpTreeLevel(input logic [3:0] level, output logic en);
  genvar i;
  logic [3:0] sel;
  generate
    for (i = 0; i < 4; i = i + 1) begin : lvl_loop
      assign sel[i] = (level == i);
    end
  endgenerate
  assign en = |sel;
endmodule
module dumpTreeJsonLevel(input logic [7:0] depth, output logic [3:0] code);
  typedef struct packed { logic [7:0] d; logic [3:0] c; } info_t;
  info_t info;
  always_comb begin
    info.d = depth;
    info.c = depth[3:0];
    code = info.c;
  end
endmodule
module dumpTreeEitherLevel(input logic [7:0] val, output logic flag);
  typedef union packed { logic [7:0] byte_data; logic [7:0] bit_data; } u_t;
  u_t u;
  always_comb begin
    u.byte_data = val;
    flag = |u.bit_data;
  end
endmodule
module mod_deleting(input logic clk, output logic deleted);
  logic [3:0] cnt;
  function logic should_delete(input logic [3:0] cnt_in);
    should_delete = (cnt_in == 4);
  endfunction
  always_ff @(posedge clk) begin
    deleted <= should_delete(cnt);
  end
endmodule
module mod_checkAll(input logic [1:0] sel, output logic inc);
  logic [3:0] arr [0:3];
  always_comb begin
    inc = 0;
    for (int i = 0; i < 4; i = i + 1) begin
      arr[i] = i;
      inc |= (arr[i] == sel);
    end
  end
endmodule
module mod_checkDType(input logic generic, input logic kill, output logic to_elim);
  assign to_elim = (!generic && kill);
endmodule
module visit_AstNodeModule(input logic en, output logic incp);
  parameter bit modPublic = 1;
  logic [3:0] usr1;
  always_comb begin
    if (en && modPublic) usr1 = usr1 + 1;
    incp = (usr1 != 0);
  end
endmodule
module visit_AstCFunc(input logic scope_exist, output logic incp);
  function logic calc_inc(input logic x);
    calc_inc = x;
  endfunction
  assign incp = calc_inc(scope_exist);
endmodule
module visit_AstScope(input logic [1:0] above_scope, input logic is_top, output logic dead);
  assign dead = (!is_top && (above_scope == 2'b00));
endmodule
module visit_AstCell(input logic in_ref, output logic incp);
  logic [3:0] vec;
  always_comb begin
    vec = in_ref ? 4'b0001 : 4'b0000;
    incp = in_ref && vec[0];
  end
endmodule
module visit_AstNodeVarRef(input logic [7:0] var_scope, input logic var_exist, output logic inc);
  assign inc = var_exist | var_scope[0];
endmodule
module visit_AstNodeFTaskRef(input logic elim_cells, output logic c_pkg_out, output logic inc);
  always_comb begin
    if (elim_cells) c_pkg_out = 1'b0;
    else inc = c_pkg_out;
  end
endmodule
module visit_AstMethodCall(input logic in_sig, output logic out_sig);
  assign out_sig = in_sig;
endmodule
module visit_AstRefDType(input logic class_exist, input logic elim_cells, output logic inc);
  always_comb begin
    if (!class_exist) inc = 1'b0;
    else if (elim_cells) inc = 1'b0;
    else inc = 1'b1;
  end
endmodule
module visit_AstClassRefDType(input logic [3:0] classp, input logic exist, output logic inc);
  assign inc = exist && classp[0];
endmodule
module visit_AstIfaceRefDType(input logic modport_exist, input logic elim_cells, input logic ifaceViaCell, output logic inc);
  always_comb begin
    if (elim_cells) inc = 1'b0;
    else inc = (modport_exist || ifaceViaCell);
  end
endmodule
module visit_AstNodeDType(input logic generic, input logic undead, output logic put_elim);
  assign put_elim = (!generic && !undead);
endmodule
module visit_AstEnumItemRef(input logic elim_cells, output logic c_pkg_out, output logic inc);
  always_comb begin
    if (elim_cells) c_pkg_out = 1'b0;
    inc = !elim_cells;
  end
endmodule
module visit_AstMemberSel(input logic [7:0] varp_dtype, output logic inc);
  assign inc = varp_dtype[0];
endmodule
module visit_AstStructSel(input logic [7:0] dtype_val, output logic inc);
  assign inc = dtype_val[1];
endmodule
module visit_AstModport(input logic elim_cells, input logic has_vars, output logic alive);
  assign alive = (!elim_cells || has_vars);
endmodule
module visit_AstSelLoopVars(input logic [3:0] cnt, output logic inc);
  assign inc = (cnt != 0);
endmodule
module visit_AstTypedef(input logic attrPublic, input logic isPkg, output logic inc);
  assign inc = attrPublic && isPkg;
endmodule
module visit_AstVarScope(input logic [3:0] scopep_val, input logic varp_elim, output logic dead);
  assign dead = varp_elim;
endmodule
module visit_AstVar(input logic isSigPublic, input logic in_selloop, input logic isTemp, input logic isTrace, input logic elimUserVars, output logic dead);
  assign dead = (!isSigPublic && !in_selloop && ((isTemp && !isTrace) || elimUserVars));
endmodule
module visit_AstNodeAssign(input logic [7:0] lhs, input logic [7:0] rhs, input logic fDeadAssigns, output logic canElim);
  assign canElim = (rhs == 8'b0 && fDeadAssigns);
endmodule
module visit_AstClockingItem(input logic inClk, output logic out);
  assign out = inClk;
endmodule
module visit_AstNodeGeneric(input logic in_pure, output logic sideEffect);
  assign sideEffect = !in_pure;
endmodule
module mod_deadCheckTypedefs(input logic [3:0] member_count, input logic isPacked, input logic attrPublic, input logic m_elimCells, output logic killTypedef);
  assign killTypedef = (m_elimCells && !attrPublic && (member_count == 0 || isPacked));
endmodule
module mod_deadCheckMod(input logic [2:0] level, input logic isInternal, input logic user1_zero, output logic killMod);
  assign killMod = (level > 3'd2 && user1_zero && !isInternal);
endmodule
module mod_mightElimVar(input logic isSigPublic, input logic isIO, input logic isClassMember, input logic sensIface, input logic isTemp, input logic isTrace, input logic elimUserVars, output logic mightElim);
  assign mightElim = (!isSigPublic && !isIO && !isClassMember && !sensIface && ((isTemp && !isTrace) || elimUserVars));
endmodule
module mod_deadCheckScope(input logic [3:0] scp_user1, input logic aboveScopep_exists, input logic dtypep_exists, output logic killScope);
  assign killScope = (scp_user1 == 4'b0000);
endmodule
module mod_deadCheckCells(input logic fDeadCells, input logic user1_zero, input logic stmtsp_exists, output logic killCell);
  assign killCell = (user1_zero && !stmtsp_exists && fDeadCells);
endmodule
module mod_deadCheckClasses(input logic [3:0] cls_user1, input logic extend_exists, input logic classOrPkg_exists, output logic killClass);
  assign killClass = (cls_user1 == 4'b0000);
endmodule
module mod_deadCheckVar(input logic vscp_user1, input logic [7:0] assign_count, input logic dtypep_exists, input logic scopep_exists, output logic killVarScope);
  assign killVarScope = (vscp_user1 == 1'b0);
endmodule
module mod_preserveTopIfaces(input logic [2:0] level, input logic isIfaceRef, input logic ifacep_user1, output logic setUser1);
  assign setUser1 = (level <= 3'd2 && isIfaceRef && ifacep_user1 == 1'b0);
endmodule
module mod_deadifyModules(input logic elimUserVars, input logic elimDTypes, input logic elimScopes, input logic elimCells, input logic elimTopIfaces, output logic called);
  assign called = (!elimTopIfaces);
endmodule
module mod_deadifyDTypes(input logic elimUserVars, input logic elimDTypes, input logic elimScopes, input logic elimCells, input logic elimTopIfaces, output logic called);
  assign called = elimDTypes;
endmodule
module mod_deadifyDTypesScoped(input logic elimUserVars, input logic elimDTypes, input logic elimScopes, input logic elimCells, input logic elimTopIfaces, output logic called);
  assign called = (elimDTypes && elimScopes);
endmodule
module mod_deadifyAll(input logic elimUserVars, input logic elimDTypes, input logic elimScopes, input logic elimCells, input logic elimTopIfaces, output logic called);
  assign called = (elimUserVars && elimDTypes && elimCells && !elimTopIfaces);
endmodule
module mod_deadifyAllScoped(input logic elimUserVars, input logic elimDTypes, input logic elimScopes, input logic elimCells, input logic elimTopIfaces, output logic called);
  assign called = (elimUserVars && elimDTypes && elimScopes && elimCells);
endmodule
