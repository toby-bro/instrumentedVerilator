class MyAstNode;
    rand int id;
    rand int data_val;
    rand int hash_val;
    function new(int p_id, int p_data, int p_hash);
        id = p_id;
        data_val = p_data;
        hash_val = p_hash;
    endfunction
    function automatic bit isSameUserCheck(MyAstNode other_node);
        return (this.data_val == other_node.data_val && this.id != other_node.id);
    endfunction
    function automatic bit sameTreeCheck(MyAstNode other_node);
        return (this.data_val == other_node.data_val && this.hash_val == other_node.hash_val);
    endfunction
endclass
module DupEraseSim (
    input logic [7:0] in_data_arr [0:7],
    input logic [7:0] target_value,
    output logic [7:0] out_data_arr [0:7],
    output logic       erased_flag
);
    logic [7:0] temp_arr [0:7];
    always_comb begin
        erased_flag = 1'b0;
        for (int i = 0; i < 8; i++) begin
            temp_arr[i] = in_data_arr[i];
        end
        for (int i = 0; i < 8; i++) begin
            if (temp_arr[i] == target_value) begin
                temp_arr[i] = 8'h00;
                erased_flag = 1'b1;
            end
        end
        for (int i = 0; i < 8; i++) begin
            out_data_arr[i] = temp_arr[i];
        end
    end
endmodule
module DupFindSim (
    input logic [7:0] query_id,
    input logic [7:0] query_data,
    input logic [7:0] query_hash,
    output logic       duplicate_found,
    output int         duplicate_idx
);
    MyAstNode nodes_list[10];
    MyAstNode query_node_inst;
    always_comb begin
        duplicate_found = 1'b0;
        duplicate_idx = -1;
        nodes_list[0] = new(1, 10, 100);
        nodes_list[1] = new(2, 20, 200);
        nodes_list[2] = new(3, 10, 100);
        nodes_list[3] = new(4, 30, 300);
        nodes_list[4] = new(5, 10, 150);
        nodes_list[5] = new(6, 40, 400);
        nodes_list[6] = new(7, 20, 200);
        nodes_list[7] = new(8, 50, 500);
        nodes_list[8] = new(9, 10, 100);
        nodes_list[9] = new(10, 60, 600);
        query_node_inst = new(query_id, query_data, query_hash);
        for (int i = 0; i < 10; i++) begin
            if (nodes_list[i] == null) continue;
            if (query_node_inst.id == nodes_list[i].id) begin
                continue;
            end
            if (!query_node_inst.isSameUserCheck(nodes_list[i])) begin
                continue;
            end
            if (!query_node_inst.sameTreeCheck(nodes_list[i])) begin
                continue;
            end
            duplicate_found = 1'b1;
            duplicate_idx = i;
            break;
        end
    end
endmodule
module DupStatsSim (
    input logic [7:0] input_hashes [0:16],
    output int         total_buckets,
    output int         max_bucket_size,
    output int         sum_of_occurrences
);
    int dist_map[int];
    logic [7:0] lasthash_sv;
    int num_in_bucket_sv;
    always_comb begin
        total_buckets = 0;
        max_bucket_size = 0;
        sum_of_occurrences = 0;
        dist_map.delete();
        lasthash_sv = 8'hFF;
        num_in_bucket_sv = 0;
        for (int i = 0; i <= 16; i++) begin
            logic is_cend_local;
            logic hash_changed_local;
            is_cend_local = (i == 16);
            hash_changed_local = (i < 16 && i > 0 && input_hashes[i] != lasthash_sv);
            if (is_cend_local || hash_changed_local) begin
                if (num_in_bucket_sv > 0) begin
                    dist_map[num_in_bucket_sv]++;
                end
                num_in_bucket_sv = 0;
            end
            if (is_cend_local) break;
            lasthash_sv = input_hashes[i];
            num_in_bucket_sv++;
        end
        total_buckets = dist_map.num();
        foreach (dist_map[key_bucket_size]) begin
            int count_occurrences;
            count_occurrences = dist_map[key_bucket_size];
            if (key_bucket_size > max_bucket_size) begin
                max_bucket_size = key_bucket_size;
            end
            sum_of_occurrences += count_occurrences;
        end
    end
endmodule
module DumpLevelSim (
    input logic debug_level_enabled,
    output logic dump_action_taken
);
    task automatic perform_dump_action();
        dump_action_taken = 1'b1;
    endtask
    always_comb begin
        dump_action_taken = 1'b0;
        if (debug_level_enabled) begin
            perform_dump_action();
        end
    end
endmodule
