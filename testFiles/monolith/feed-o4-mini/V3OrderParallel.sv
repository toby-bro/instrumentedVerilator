module PartCheck(input  logic [63:0] cached, input  logic [63:0] actual, output logic ok);
  localparam bit PART_STEPPED_COST = 1;
  always_comb begin
    if (PART_STEPPED_COST) begin
      ok = ((cached * 10 <= actual * 11) && (cached * 11 >= actual * 10));
    end else begin
      ok = (cached == actual);
    end
  end
endmodule
module EdgeKeyCompare(input  logic [63:0] score_a, input logic [63:0] id_a,
                      input  logic [63:0] score_b, input logic [63:0] id_b,
                      output logic less);
  always_comb less = (score_a < score_b) || ((score_a == score_b) && (id_a < id_b));
endmodule
module MergeCandidateKeyCompare(input  logic [63:0] score_a, input logic [63:0] id_a,
                                input  logic [63:0] score_b, input logic [63:0] id_b,
                                output logic less);
  always_comb less = (score_a > score_b) || ((score_a == score_b) && (id_a > id_b));
endmodule
module StepCost #(parameter STEPPED = 1) (
  input  logic [63:0] cost,
  output logic [63:0] stepCostOut
);
  function automatic logic [63:0] compute(input logic [63:0] c);
    real logc;
    real r;
    integer  ci;
    if (STEPPED) begin
      if (c == 0) begin
        compute = 0;
      end else begin
        logc = $ln(c);
        r    = $ceil(logc * 20.0) / 20.0;
        compute = $rtoi($exp(r));
      end
    end else begin
      compute = c;
    end
  endfunction
  assign stepCostOut = compute(cost);
endmodule
module SiblingScore(
  input  logic [63:0] fwd_a, input logic [63:0] fwd_b,
  input  logic [63:0] rev_a, input logic [63:0] rev_b,
  input  logic [63:0] cost_a, input logic [63:0] cost_b,
  output logic [63:0] score
);
  logic [63:0] maxFwd, maxRev, sumCost;
  always_comb begin
    maxFwd  = (fwd_a > fwd_b) ? fwd_a : fwd_b;
    maxRev  = (rev_a > rev_b) ? rev_a : rev_b;
    sumCost = cost_a + cost_b;
    score   = maxRev + maxFwd + sumCost;
  end
endmodule
module EdgeScore(
  input  logic [63:0] from_fwd,      input logic [63:0] to_without,
  input  logic [63:0] from_without,  input logic [63:0] to_rev,
  input  logic [63:0] cost_from,     input logic [63:0] cost_to,
  output logic [63:0] score
);
  logic [63:0] maxFwd, maxRev, sumCost;
  always_comb begin
    maxFwd  = (from_fwd > to_without) ? from_fwd : to_without;
    maxRev  = (from_without > to_rev) ? from_without : to_rev;
    sumCost = cost_from + cost_to;
    score   = maxRev + maxFwd + sumCost + 1;
  end
endmodule
module NewCp #(parameter DIR = 0) (
  input  logic [63:0] cp_self,
  input  logic [63:0] cp_other,
  input  logic [63:0] cost_self,
  input  logic [63:0] cost_other,
  input  logic        merge_edge,
  output logic [63:0] cp_out,
  output logic        propagate,
  output logic [63:0] propagateCp
);
  logic [63:0] ncp, origRel, newRel;
  always_comb begin
    if (merge_edge) begin
      if (DIR == 1) begin
        ncp = (cp_other > cp_self) ? cp_other : cp_self;
      end else begin
        ncp = (cp_self > cp_other) ? cp_self : cp_other;
      end
    end else begin
      ncp = (cp_self > cp_other) ? cp_self : cp_other;
    end
    origRel     = cp_self + cost_self;
    propagateCp = ncp + (cost_self + cost_other);
    cp_out      = ncp;
    propagate   = (propagateCp > origRel);
  end
endmodule
module SiblingLimit #(parameter LIMIT = 26) (
  input  logic [$clog2(LIMIT+1)-1:0] count,
  output logic limited
);
  always_comb limited = (count >= LIMIT);
endmodule
