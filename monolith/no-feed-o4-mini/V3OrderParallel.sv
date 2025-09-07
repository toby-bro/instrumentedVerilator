`ifndef PART_STEPPED_COST
  `define PART_STEPPED_COST
`endif
module partCheckModule(input logic [63:0] cached, input logic [63:0] actual, output logic ok);
  always_comb begin
    `ifdef PART_STEPPED_COST
      ok = ((cached * 10 <= actual * 11) && (cached * 11 >= actual * 10));
      assert(ok);
    `else
      ok = (cached == actual);
      assert(ok);
    `endif
  end
endmodule
module edgeKeyModule(
  input logic [63:0] id_a, input logic [63:0] score_a,
  input logic [63:0] id_b, input logic [63:0] score_b,
  output logic lt);
  typedef struct packed { logic [63:0] m_id; logic [63:0] m_score; } EdgeKey_t;
  always_comb begin
    EdgeKey_t a, b;
    a.m_id = id_a; a.m_score = score_a;
    b.m_id = id_b; b.m_score = score_b;
    lt = (a.m_score < b.m_score) || (a.m_score == b.m_score && a.m_id < b.m_id);
  end
endmodule
module mergeCandidateModule(
  input logic is_sibling_in,
  input logic [31:0] score_in,
  output logic is_sib_out,
  output logic is_edge_out,
  output logic [31:0] score_out);
  class MergeCandidate;
    bit m_isSibling;
    logic [31:0] m_score;
    function new(bit isSibling, logic [31:0] score);
      m_isSibling = isSibling; m_score = score;
    endfunction
    function bit isSiblingMC(); return m_isSibling; endfunction
    virtual function bit mergeWouldCreateCycle();
      return m_isSibling ? 0 : 1;
    endfunction
    virtual function void rescore();
      if (m_isSibling) m_score = m_score + 10;
      else m_score = m_score + 1;
    endfunction
  endclass
  class SiblingMC extends MergeCandidate;
    function new(logic [31:0] score);
      super.new(1, score);
    endfunction
  endclass
  class MTaskEdge extends MergeCandidate;
    function new(logic [31:0] score);
      super.new(0, score);
    endfunction
    function bit mergeWouldCreateCycle();
      return 1;
    endfunction
  endclass
  always_comb begin
    MergeCandidate cand_sib = new SiblingMC(score_in);
    MergeCandidate cand_edge = new MTaskEdge(score_in);
    is_sib_out = cand_sib.isSiblingMC();
    is_edge_out = !cand_edge.isSiblingMC();
    cand_sib.rescore();
    score_out = cand_sib.m_score;
  end
endmodule
module mtaskEdgeModule(
  input logic cycle_in,
  output logic cycle_out);
  class MTaskEdge;
    bit m_cycleMarker;
    function new(bit cycleFlag);
      m_cycleMarker = cycleFlag;
    endfunction
    function bit mergeWouldCreateCycle();
      return m_cycleMarker;
    endfunction
    function void resetCriticalPaths();
      m_cycleMarker = 0;
    endfunction
  endclass
  always_comb begin
    MTaskEdge me = new(cycle_in);
    cycle_out = me.mergeWouldCreateCycle();
    me.resetCriticalPaths();
  end
endmodule
module logicMTaskModule(
  input logic [31:0] cost_in,
  output logic [31:0] cost_out);
  class LogicMTask;
    static int s_nextId = 1;
    int m_id;
    function new();
      m_id = s_nextId; s_nextId++;
    endfunction
    static function int stepCost(int cost);
      `ifdef PART_STEPPED_COST
        return cost;
      `else
        return cost;
      `endif
    endfunction
  endclass
  always_comb begin
    LogicMTask task = new;
    cost_out = LogicMTask::stepCost(cost_in);
  end
endmodule
module partInitHalfModule #(
  parameter int N_Way = 0
)(
  input logic start,
  output logic done
);
  localparam int rev = N_Way ? 0 : 1;
  always_comb begin
    done = start;
  end
endmodule
module propagateCpModule #(
  parameter int N_Way = 0,
  parameter bit slowAsserts = 0
)(
  input logic trigger,
  output logic finished
);
  class PendingKey;
    logic [31:0] m_score;
    function new(logic [31:0] score);
      m_score = score;
    endfunction
    function bit lessThan(PendingKey other);
      return m_score < other.m_score;
    endfunction
  endclass
  class PropagateCp;
    PendingKey queue[$];
    function new();
    endfunction
    function void cpHasIncreased(logic [31:0] newCp);
      queue.push_back(new PendingKey(newCp));
    endfunction
    function void go();
      if (!queue.empty()) queue.pop_front();
    endfunction
  endclass
  always_comb begin
    PropagateCp propagator = new;
    propagator.cpHasIncreased(1);
    propagator.go();
    finished = 1;
  end
endmodule
module redirectEdgesModule(
  input logic start,
  output logic done
);
  always_comb begin
    done = start;
  end
endmodule
module contractionModule(
  input logic [31:0] cost_a,
  input logic [31:0] cost_b,
  output logic [31:0] new_cp,
  output logic do_propagate
);
  function automatic void newCp(
    input logic [31:0] a,
    input logic [31:0] b,
    output logic [31:0] cp,
    output logic propagate
  );
    cp = (a > b) ? a : b;
    propagate = (cp > (a + b));
  endfunction
  always_comb begin
    newCp(cost_a, cost_b, new_cp, do_propagate);
  end
endmodule
module siblingPairModule(
  input logic [7:0] n,
  input logic [7:0] ids [0:25],
  output logic valid_pairs [0:25]
);
  typedef struct {
    logic [31:0] m_cp;
    logic [7:0]  m_id;
    logic [7:0]  m_idx;
  } SortingRecord;
  SortingRecord sortRecs[0:25];
  integer i;
  always_comb begin
    for (i = 0; i < n; i++) begin
      sortRecs[i].m_id  = ids[i];
      sortRecs[i].m_cp  = ids[i];
      sortRecs[i].m_idx = i;
      valid_pairs[i]   = 0;
    end
    if (n >= 2) begin
      if (sortRecs[0].m_cp > sortRecs[1].m_cp) begin
        SortingRecord tmp = sortRecs[0];
        sortRecs[0] = sortRecs[1];
        sortRecs[1] = tmp;
      end
      valid_pairs[0] = 1;
    end
  end
endmodule
