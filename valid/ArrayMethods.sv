module array_reduction_demo (
    input  logic        clk,
    output logic [31:0] sum_out,
    output logic [31:0] or_out,
    output logic [31:0] and_out,
    output logic [31:0] xor_out,
    output logic [31:0] product_out
);
    int arr[5] = '{1, 2, 3, 4, 5};
    always_comb begin
        sum_out     = arr.sum();
        or_out      = arr.or();
        and_out     = arr.and();
        xor_out     = arr.xor();
        product_out = arr.product();
    end
endmodule
module array_sort_reverse_demo (
    input  logic        clk,
    output logic [31:0] first_sorted,
    output logic [31:0] first_rsorted,
    output logic [31:0] first_reversed
);
    int dyn_q[$] = {5, 1, 4, 2, 3};
    always_ff @(posedge clk) begin
        dyn_q.sort();
        first_sorted   <= dyn_q[0];
        dyn_q.reverse();
        if (dyn_q.size() != 0)
            first_reversed <= dyn_q[0];
        dyn_q.rsort();
        if (dyn_q.size() != 0)
            first_rsorted  <= dyn_q[0];
    end
endmodule
module array_locator_demo (
    input  logic        clk,
    output logic [31:0] first_even_idx,
    output logic [31:0] last_even_idx
);
    int q[$] = {1, 2, 3, 4, 5, 6};
    int idx_q[$];
    always_ff @(posedge clk) begin
        idx_q = q.find_first_index with (item % 2 == 0);
        first_even_idx <= (idx_q.size() > 0) ? idx_q[0] : 32'hFFFF_FFFF;
        idx_q = q.find_last_index with (item % 2 == 0);
        last_even_idx  <= (idx_q.size() > 0) ? idx_q[0] : 32'hFFFF_FFFF;
    end
endmodule
module array_minmax_unique_demo (
    input  logic        clk,
    output logic [31:0] min_elem,
    output logic [31:0] max_elem,
    output logic [31:0] unique_count
);
    int q[$] = {3, 1, 4, 1, 5, 9, 2, 6, 5};
    int res_q[$];
    always_ff @(posedge clk) begin
        res_q   = q.min();
        min_elem <= (res_q.size() > 0) ? res_q[0] : 0;
        res_q   = q.max();
        max_elem <= (res_q.size() > 0) ? res_q[0] : 0;
        res_q        = q.unique();
        unique_count <= res_q.size();
    end
endmodule
module array_size_demo (
    input  logic        dummy_in,
    output logic [31:0] size_out
);
    parameter int static_arr[4] = '{10, 20, 30, 40};
    localparam int static_size  = $size(static_arr);
    assign size_out = static_size;
endmodule
module dyn_array_delete_demo (
    input  logic        clk,
    output logic [31:0] size_after_del
);
    int darr[];
    always_ff @(posedge clk) begin
        darr = new[3];
        darr = '{7, 8, 9};
        darr.delete();
        size_after_del <= darr.size();
    end
endmodule
module assoc_array_exists_demo (
    input  logic        clk,
    output logic        exists_flag
);
    int aa[string];
    always_ff @(posedge clk) begin
        aa["hello"] = 42;
        exists_flag <= aa.exists("hello");
    end
endmodule
module queue_push_pop_demo (
    input  logic        clk,
    output logic [31:0] popped_val
);
    int q[$];
    always_ff @(posedge clk) begin
        q.push_back(100);
        q.push_back(200);
        popped_val <= q.pop_front();
    end
endmodule
module queue_insert_delete_demo (
    input  logic        clk,
    output logic [31:0] q_size
);
    int q[$];
    always_ff @(posedge clk) begin
        q.push_back(10);
        q.push_back(30);
        q.insert(1, 20);
        q.delete(0);
        q_size <= q.size();
    end
endmodule
module iterator_index_demo (
    input  logic        clk,
    output logic [31:0] last_idx
);
    int fixed_arr[4] = '{11, 22, 33, 44};
    always_ff @(posedge clk) begin
        foreach (fixed_arr[i]) begin
            last_idx <= i.index();
        end
    end
endmodule
