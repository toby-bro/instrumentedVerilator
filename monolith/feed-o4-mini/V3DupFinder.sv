module erase_mod(input logic [7:0] node, input logic [63:0] bucket_flat, input logic [3:0] bucket_count, output logic erased);
  integer i;
  always_comb begin
    erased = 0;
    for (i = 0; i < bucket_count; i = i + 1) begin
      if (bucket_flat[8*i +:8] == node)
        erased = 1;
    end
  end
endmodule
module finddup_mod(input logic [7:0] node, input logic [63:0] others_flat, input logic [3:0] count, input logic check_enable, input logic [15:0] flags_flat, output logic dup_found);
  integer i;
  logic [7:0] curr;
  always_comb begin
    dup_found = 0;
    for (i = 0; i < count; i = i + 1) begin
      curr = others_flat[8*i +:8];
      if (curr == node) continue;
      if (check_enable && !flags_flat[i]) continue;
      dup_found = 1;
    end
  end
endmodule
module dump_mod(input logic [127:0] hashes_flat, input logic [4:0] hash_len, output logic [127:0] dist_flat, output logic [4:0] dist_len);
  integer i;
  integer num_in_bucket;
  logic [7:0] last_hash;
  logic [7:0] curr_hash;
  always_comb begin
    for (i = 0; i < 16; i = i + 1)
      dist_flat[8*i +:8] = 0;
    if (hash_len == 0) begin
      dist_len = 0;
    end else begin
      last_hash = hashes_flat[0 +:8];
      num_in_bucket = 0;
      for (i = 0; i < hash_len; i = i + 1) begin
        curr_hash = hashes_flat[8*i +:8];
        if (i == 0 || curr_hash != last_hash) begin
          if (num_in_bucket > 0)
            dist_flat[8*num_in_bucket +:8] = dist_flat[8*num_in_bucket +:8] + 1;
          last_hash = curr_hash;
          num_in_bucket = 1;
        end else begin
          num_in_bucket = num_in_bucket + 1;
        end
      end
      if (num_in_bucket > 0)
        dist_flat[8*num_in_bucket +:8] = dist_flat[8*num_in_bucket +:8] + 1;
      dist_len = 16;
    end
  end
endmodule
module dump_pref_mod(input logic [4:0] level, input logic [127:0] hashes_flat, input logic [4:0] hash_len, output logic [127:0] dist_flat, output logic [4:0] dist_len);
  integer i;
  integer num_in_bucket;
  logic [7:0] last_hash;
  logic [7:0] curr_hash;
  function bit dumpLevel(input logic [4:0] lvl);
    return lvl > 0;
  endfunction
  always_comb begin
    if (dumpLevel(level) && hash_len != 0) begin
      for (i = 0; i < 16; i = i + 1)
        dist_flat[8*i +:8] = 0;
      last_hash = hashes_flat[0 +:8];
      num_in_bucket = 0;
      for (i = 0; i < hash_len; i = i + 1) begin
        curr_hash = hashes_flat[8*i +:8];
        if (i == 0 || curr_hash != last_hash) begin
          if (num_in_bucket > 0)
            dist_flat[8*num_in_bucket +:8] = dist_flat[8*num_in_bucket +:8] + 1;
          last_hash = curr_hash;
          num_in_bucket = 1;
        end else begin
          num_in_bucket = num_in_bucket + 1;
        end
      end
      if (num_in_bucket > 0)
        dist_flat[8*num_in_bucket +:8] = dist_flat[8*num_in_bucket +:8] + 1;
      dist_len = 16;
    end else begin
      for (i = 0; i < 16; i = i + 1)
        dist_flat[8*i +:8] = 0;
      dist_len = 0;
    end
  end
endmodule
module class_mod(input logic [7:0] node_id, input logic [3:0] count_ids, input logic [63:0] id_list_flat, output logic same_found);
  class AstNode;
    rand logic [7:0] id;
    function new(logic [7:0] id_in);
      id = id_in;
    endfunction
    function bit sameTree(AstNode other);
      return id == other.id;
    endfunction
  endclass
  class DupFinder;
    AstNode items[$];
    function void add(AstNode n);
      items.push_back(n);
    endfunction
    function bit findDup(AstNode nodep);
      integer j;
      for (j = 0; j < items.size(); j = j + 1) begin
        if (items[j].id == nodep.id) continue;
        if (items[j].sameTree(nodep)) return 1;
      end
      return 0;
    endfunction
  endclass
  DupFinder finder;
  integer i;
  AstNode n;
  AstNode test_node;
  always_comb begin
    finder = new();
    for (i = 0; i < count_ids; i = i + 1) begin
      n = new(id_list_flat[8*i +:8]);
      finder.add(n);
    end
    test_node = new(node_id);
    same_found = finder.findDup(test_node);
  end
endmodule
