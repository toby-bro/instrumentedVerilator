module gather_affinity_demo #(parameter ID_WIDTH=4) (
  input  logic [ID_WIDTH-1:0] var_ref,
  output logic [ID_WIDTH-1:0] affinity
);
  class Visitor;
    pure virtual function void visit_var_ref(logic [ID_WIDTH-1:0] mask, output logic [ID_WIDTH-1:0] out);
    pure virtual function void visit_cfunc(logic call_flag, output logic [ID_WIDTH-1:0] out);
    pure virtual function void visit_ccall(logic call_enable, output logic [ID_WIDTH-1:0] out);
    pure virtual function void visit_node(logic valid, output logic [ID_WIDTH-1:0] out);
  endclass
  final class GatherMTaskAffinity extends Visitor;
    const logic [ID_WIDTH-1:0] id;
    function new(logic [ID_WIDTH-1:0] mtid);
      id = mtid;
    endfunction
    function void visit_var_ref(logic [ID_WIDTH-1:0] mask, output logic [ID_WIDTH-1:0] out);
      if (mask[id]) out = mask;
      else           out = '0;
    endfunction
    function void visit_cfunc(logic call_flag, output logic [ID_WIDTH-1:0] out);
      if (call_flag) out = {ID_WIDTH{1'b1}};
      else           out = '0;
    endfunction
    function void visit_ccall(logic call_enable, output logic [ID_WIDTH-1:0] out);
      if (call_enable) out = mask; else out = id;
    endfunction
    function void visit_node(logic valid, output logic [ID_WIDTH-1:0] out);
      if (valid) out = var_ref; else out = id;
    endfunction
  endclass
  always_comb begin
    GatherMTaskAffinity ga = new(var_ref);
    ga.visit_var_ref(var_ref, affinity);
  end
endmodule
module tsp_sorter_demo #(parameter N=4) (
  input  logic [N-1:0] vec1,
  input  logic [N-1:0] vec2,
  output int           cost_out,
  output bit           lt_flag
);
  virtual class TspStateBase;
    pure virtual function bit lt(ref TspStateBase other);
    pure virtual function int cost(ref TspStateBase other);
  endclass
  class VarTspSorter extends TspStateBase;
    static int serialNext = 0;
    int serial;
    logic [N-1:0] mTaskIds;
    function new(logic [N-1:0] ids);
      serial = serialNext + 1;
      serialNext = serial;
      mTaskIds = ids;
    endfunction
    function bit lt(ref TspStateBase other);
      VarTspSorter o = VarTspSorter::cast(other);
      return serial < o.serial;
    endfunction
    function int cost(ref TspStateBase other);
      VarTspSorter o = VarTspSorter::cast(other);
      int c = 0;
      for (int i = 0; i < N; i++) c += mTaskIds[i] ^ o.mTaskIds[i];
      return c;
    endfunction
  endclass
  always_comb begin
    VarTspSorter a = new(vec1);
    VarTspSorter b = new(vec2);
    cost_out = a.cost(b);
    lt_flag  = a.lt(b);
  end
endmodule
module var_attributes_demo (
  input  logic        clk_en,
  input  logic [15:0] sigbytes,
  input  logic        isHierChild,
  input  logic        isPrimaryIO,
  input  logic        isUsedClock,
  input  logic        widthMin1,
  input  logic        isUnpackArray,
  input  logic        isOpaque,
  input  logic        isScBv,
  input  logic        isScBigUint,
  output logic [7:0]  stratum,
  output logic        anonOk
);
  typedef struct packed { logic [7:0] stratum; bit anonOk; } VarAttributes;
  function VarAttributes computeAttr();
    VarAttributes attr;
    if (isHierChild && isPrimaryIO)         attr.stratum = 0;
    else if (isUsedClock && widthMin1)      attr.stratum = 1;
    else if (isUnpackArray)                 attr.stratum = 9;
    else if (isOpaque)                      attr.stratum = 8;
    else if (isScBv || isScBigUint)         attr.stratum = 7;
    else if (sigbytes == 8)                 attr.stratum = 6;
    else if (sigbytes == 4)                 attr.stratum = 5;
    else if (sigbytes == 2)                 attr.stratum = 3;
    else if (sigbytes == 1)                 attr.stratum = 2;
    else                                    attr.stratum = 10;
    attr.anonOk = clk_en;
    return attr;
  endfunction
  always_comb begin
    VarAttributes v = computeAttr();
    stratum = v.stratum;
    anonOk  = v.anonOk;
  end
endmodule
module simple_sorter_demo (
  input  logic [31:0] arr_in [0:3],
  output logic [31:0] arr_out[0:3]
);
  typedef struct { logic [31:0] val; bit isStatic; bit anonOk; logic [7:0] stratum; } Var;
  Var list[0:3];
  function int compare(Var a, Var b);
    if (a.isStatic != b.isStatic) return b.isStatic - a.isStatic;
    if (a.anonOk    != b.anonOk)    return a.anonOk    - b.anonOk;
    return (a.stratum < b.stratum) ? -1 : ((a.stratum > b.stratum) ? 1 : 0);
  endfunction
  always_comb begin
    for (int i = 0; i < 4; i++) begin
      list[i].val     = arr_in[i];
      list[i].isStatic= arr_in[i][0];
      list[i].anonOk  = arr_in[i][1];
      list[i].stratum = arr_in[i][7:0];
    end
    for (int i = 0; i < 4; i++) begin
      for (int j = i+1; j < 4; j++) begin
        if (compare(list[i], list[j]) > 0) begin
          Var tmp    = list[i];
          list[i]    = list[j];
          list[j]    = tmp;
        end
      end
    end
    for (int i = 0; i < 4; i++) arr_out[i] = list[i].val;
  end
endmodule
module associative_array_demo (
  input  logic [3:0]     keys [0:3],
  input  logic [7:0]     vals [0:3],
  output logic [7:0]     sum_vals
);
  logic [7:0] assoc_array [logic [3:0]];
  always_comb begin
    sum_vals = 0;
    for (int i = 0; i < 4; i++) assoc_array[keys[i]] = vals[i];
    foreach (assoc_array[k]) sum_vals += assoc_array[k];
  end
endmodule
module foreach_demo (
  input  logic [7:0] data_in,
  output logic [7:0] rotated,
  output int         popcount
);
  always_comb begin
    rotated  = {data_in[0], data_in[7:1]};
    popcount = 0;
    foreach (data_in[i]) begin
      popcount += data_in[i];
    end
  end
endmodule
module generate_demo (
  input  logic [7:0] bus_in,
  output logic [7:0] bus_out
);
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : bit_rev
      assign bus_out[i] = bus_in[7-i];
    end
  endgenerate
endmodule
module parameterized_demo #(parameter WIDTH=8) (
  input  logic [WIDTH-1:0] in_vec,
  output logic [WIDTH-1:0] out_vec
);
  function logic [WIDTH-1:0] reverse_vec(input logic [WIDTH-1:0] v);
    logic [WIDTH-1:0] r;
    for (int i = 0; i < WIDTH; i++) r[i] = v[WIDTH-1-i];
    return r;
  endfunction
  always_comb begin
    out_vec = reverse_vec(in_vec);
  end
endmodule
module tsp_grouping_demo (
  input  logic [3:0] affinity0,
  input  logic [3:0] affinity1,
  input  logic [3:0] affinity2,
  input  logic [3:0] affinity3,
  input  logic [7:0] var0,
  input  logic [7:0] var1,
  input  logic [7:0] var2,
  input  logic [7:0] var3,
  output logic [7:0] sorted_vals [0:3]
);
  always_comb begin
    logic [7:0] grp1[$];
    logic [7:0] grp0[$];
    for (int i = 0; i < 4; i++) begin
      logic [3:0] aff = (i==0)? affinity0 : (i==1)? affinity1 : (i==2)? affinity2 : affinity3;
      logic [7:0] v   = (i==0)? var0       : (i==1)? var1       : (i==2)? var2       : var3;
      if (|aff) grp1.push_back(v);
      else       grp0.push_back(v);
    end
    for (int i = 0; i < grp1.size(); i++) begin
      for (int j = i+1; j < grp1.size(); j++) begin
        if (grp1[i] > grp1[j]) begin
          logic [7:0] t = grp1[i]; grp1[i] = grp1[j]; grp1[j] = t;
        end
      end
    end
    for (int i = 0; i < grp0.size(); i++) begin
      for (int j = i+1; j < grp0.size(); j++) begin
        if (grp0[i] > grp0[j]) begin
          logic [7:0] t = grp0[i]; grp0[i] = grp0[j]; grp0[j] = t;
        end
      end
    end
    int idx = 0;
    for (int k = 0; k < grp1.size() && idx < 4; k++) sorted_vals[idx++] = grp1[k];
    for (int k = 0; k < grp0.size() && idx < 4; k++) sorted_vals[idx++] = grp0[k];
    for (; idx < 4; idx++) sorted_vals[idx] = 0;
  end
endmodule
